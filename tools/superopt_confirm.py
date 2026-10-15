#!/usr/bin/env python3
"""Prove superoptimiser winners with z3 (PLAN.md §4).

Reads the JSON lines `superopt search --out FILE` writes (a harvested pattern, its leaves'
intervals and the winning circuit) and proves, for all 32-bit inputs within the intervals and
any values of the noise signals on the bus, that the circuit's output network holds exactly
the pattern's value on signal O and nothing else. The encoding follows ticky-sim's evaluator
(crates/ticky-sim/src/lib.rs) and reuses validate.py's arithmetic (`ar`, `cmpb`).

usage: tools/superopt_confirm.py RULES.jsonl [--write] [--timeout MS]
  --write   rewrite RULES.jsonl with a "proved" field per rule (unsat = proved,
            sat = counterexample, unknown)
Exit status 1 if any rule has a counterexample.
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import validate  # noqa: E402  pylint: disable=wrong-import-position
from validate import ar, cmpb, bv, z3, MIN, MAX  # noqa: E402  pylint: disable=wrong-import-position

ZERO = bv(0)
EACH, ANYTHING, EVERYTHING = "signal-each", "signal-anything", "signal-everything"
XS = ["signal-X", "signal-Y", "signal-Z"]
NOISE = ["signal-N", "signal-M"]


class Unsupported(Exception):
    """A construct the encoding doesn't cover."""


# ------------------------------------------------------------------ patterns

def parse(s):
    toks = s.replace("(", " ( ").replace(")", " ) ").split()
    pos = [0]

    def sx():
        t = toks[pos[0]]
        pos[0] += 1
        if t == "(":
            out = []
            while toks[pos[0]] != ")":
                out.append(sx())
            pos[0] += 1
            return out
        return t
    return sx()


AR = {"mul": "Mul", "div": "Div", "add": "Add", "sub": "Sub", "mod": "Mod", "pow": "Pow",
      "shl": "Shl", "shr": "Shr", "and": "And", "or": "Or", "xor": "Xor"}
CMP = {"lt": "Lt", "gt": "Gt", "eq": "Eq", "ge": "Ge", "le": "Le", "ne": "Ne"}


def const_of(e):
    if isinstance(e, str) and e not in ("_",) and not e.startswith("x"):
        return int(e)
    return None


def pat(e, xs):
    """The pattern's value as a z3 term (`_` holes are never evaluated)."""
    if isinstance(e, str):
        if e.startswith("x"):
            return xs[int(e[1:])]
        return bv(int(e))
    h = e[0]
    if h in AR:
        return ar(AR[h], pat(e[1], xs), pat(e[2], xs), const_of(e[2]))
    if h in CMP:
        return z3.If(cmpb(CMP[h], pat(e[1], xs), pat(e[2], xs)), bv(1), ZERO)
    if h == "mux":
        t, f, a, b = e[1:]
        ta = ZERO if t == "_" else z3.If(pat(t, xs) != 0, pat(a, xs), ZERO)
        fb = ZERO if f == "_" else z3.If(pat(f, xs) != 0, pat(b, xs), ZERO)
        return ta + fb
    if h == "sel":
        s = ZERO
        for c, v in zip(e[1::2], e[2::2]):
            s = s + z3.If(pat(c, xs) != 0, pat(v, xs), ZERO)
        return s
    if h == "dec":
        s = ZERO
        for arm in e[1:]:
            k, dnf = int(arm[1]), arm[2]
            terms = [z3.And([cmpb(CMP[l[0]], pat(l[1], xs), pat(l[2], xs)) for l in t[1:]]) for t in dnf[1:]]
            s = s + z3.If(z3.Or(terms) if terms else z3.BoolVal(False), bv(k), ZERO)
        return s
    raise Unsupported(h)


def complements(e, out):
    if isinstance(e, list):
        if e[0] == "mux" and isinstance(e[1], str) and isinstance(e[2], str) and e[1].startswith("x") and e[2].startswith("x"):
            out.append((int(e[1][1:]), int(e[2][1:])))
        for c in e[1:]:
            complements(c, out)
    return out


# ------------------------------------------------------------------ circuits (ticky-sim)

class Net(dict):
    def get_v(self, s):
        return self.get(s, ZERO)


def read(red, green, s, nets):
    v = ZERO
    if "R" in nets:
        v = v + red.get_v(s)
    if "G" in nets:
        v = v + green.get_v(s)
    return v


def operand(red, green, o, cur=None):
    if "const" in o:
        return bv(o["const"])
    if o["sig"] == EACH:
        return read(red, green, cur, o["nets"])
    return read(red, green, o["sig"], o["nets"])


def comb(c, red, green, universe):
    """A combinator's output {signal: term}, as ticky-sim computes it."""
    k = c["type"]
    out = {}

    def add(s, v):
        out[s] = out.get(s, ZERO) + v
    present = lambda s, nets: read(red, green, s, nets) != 0  # noqa: E731
    if k == "arith":
        f, s2 = c["first"], c["second"]
        fe, se = f.get("sig") == EACH, s2.get("sig") == EACH
        kb = s2.get("const")
        if fe or se:
            for s in universe:
                dom = z3.Or(([present(s, f["nets"])] if fe else []) + ([present(s, s2["nets"])] if se else []))
                v = ar(c["op"], operand(red, green, f, s), operand(red, green, s2, s), kb)
                if c["out"] == EACH:
                    add(s, z3.If(dom, v, ZERO))
                else:
                    add(c["out"], z3.If(dom, v, ZERO))
        else:
            add(c["out"], ar(c["op"], operand(red, green, f), operand(red, green, s2), kb))
        return out
    if k == "decider":
        conds = c["conds"]
        uses_each = any(x["first"]["sig"] == EACH or x["second"].get("sig") == EACH for x in conds)

        def holds(cur):
            groups, g = [], []
            for i, x in enumerate(conds):
                if i > 0 and not x["and"]:
                    groups.append(g)
                    g = []
                y = operand(red, green, x["second"], cur)
                fs, fn = x["first"]["sig"], x["first"]["nets"]
                if fs == EVERYTHING:
                    ok = z3.And([z3.Implies(present(s, fn), cmpb(x["cmp"], read(red, green, s, fn), y)) for s in universe])
                elif fs == ANYTHING:
                    ok = z3.Or([z3.And(present(s, fn), cmpb(x["cmp"], read(red, green, s, fn), y)) for s in universe])
                elif fs == EACH:
                    ok = cmpb(x["cmp"], read(red, green, cur, fn), y)
                else:
                    ok = cmpb(x["cmp"], read(red, green, fs, fn), y)
                g.append(ok)
            groups.append(g)
            return z3.Or([z3.And(g) for g in groups]) if conds else z3.BoolVal(False)
        if uses_each:
            nets = set()
            for x in conds:
                if x["first"]["sig"] == EACH:
                    nets.add(x["first"]["nets"])
                if x["second"].get("sig") == EACH:
                    nets.add(x["second"]["nets"])
            for s in universe:
                passing = z3.And(z3.Or([present(s, n) for n in nets]), holds(s))
                for o in c["outputs"]:
                    v = read(red, green, s, o["nets"]) if o["copy"] else bv(o["const"])
                    add(s if o["sig"] == EACH else o["sig"], z3.If(passing, v, ZERO))
        else:
            h = holds(None)
            for o in c["outputs"]:
                if o["sig"] in (EVERYTHING, EACH):
                    raise Unsupported("everything output")
                v = read(red, green, o["sig"], o["nets"]) if o["copy"] else bv(o["const"])
                add(o["sig"], z3.If(h, v, ZERO))
        return out
    raise Unsupported(k)


def confirm(rule, timeout):
    e = parse(rule["shape"])
    n = len(rule["leaves"])
    xs = [z3.BitVec(f"x{i}", 32) for i in range(n)]
    noise = [z3.BitVec(s, 32) for s in NOISE]
    assume = []
    for x, (lo, hi) in zip(xs, rule["leaves"]):
        if lo > MIN:
            assume.append(x >= lo)
        if hi < MAX:
            assume.append(x <= hi)
    for t, f in complements(e, []):
        assume.append(z3.And(z3.Or(xs[t] == 0, xs[t] == 1), xs[f] == z3.If(xs[t] == 0, bv(1), ZERO)))
    universe = XS[:n] + NOISE + ["signal-T", "signal-O"]
    green = Net({XS[i]: xs[i] for i in range(n)})
    for s, v in zip(NOISE, noise):
        green[s] = v
    P, OUT = Net(), Net()
    circ = rule["circuit"]
    for c in circ["combs"]:
        red = Net()
        if c["red"] == "P":
            red = P
        elif c["red"]:
            red = Net({s: bv(v) for s, v in c["red"]})
        for s, v in comb(c["kind"], red, green, universe).items():
            dst = P if c["to"] == "P" else OUT
            dst[s] = dst.get_v(s) + v
    if circ["offset"]:
        OUT["signal-O"] = OUT.get_v("signal-O") + bv(circ["offset"])
    goal = z3.And([OUT.get_v("signal-O") == pat(e, xs)] + [OUT.get_v(s) == 0 for s in universe if s != "signal-O"])
    sol = z3.Solver()
    sol.set("timeout", timeout)
    sol.add(assume)
    sol.add(z3.Not(goal))
    r = sol.check()
    if r == z3.sat:
        m = sol.model()
        return "sat", {str(v): m.eval(v, model_completion=True).as_signed_long() for v in xs + noise}
    return ("unsat" if r == z3.unsat else "unknown"), None


def main():
    args = sys.argv[1:]
    write = "--write" in args
    timeout = 60000
    if "--timeout" in args:
        timeout = int(args[args.index("--timeout") + 1])
    path = args[0]
    with open(path, encoding="utf-8") as f:
        rules = [json.loads(line) for line in f if line.strip()]
    bad = 0
    for r in rules:
        try:
            res, cex = confirm(r, timeout)
        except Unsupported as ex:
            res, cex = f"unsupported ({ex})", None
        r["proved"] = res
        bad += res == "sat"
        print(f"{res:8s} {r['combinators']} comb  {r['shape']}" + (f"   counterexample {cex}" if cex else ""))
    print(f"{sum(r['proved'] == 'unsat' for r in rules)} of {len(rules)} proved, {bad} counterexamples")
    if write:
        with open(path, "w", encoding="utf-8") as f:
            for r in rules:
                f.write(json.dumps(r) + "\n")
    _ = validate  # imported for its z3 set-up (re-execs into tools/.venv)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()

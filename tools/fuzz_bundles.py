#!/usr/bin/env python3
"""Fuzz bundle expressions and comprehensions against a Python model of Factorio's `each`.

Random programs combine two input bundles and a number with element-wise arithmetic and
dict comprehensions, then the compiled circuit's output (in the simulator) is compared with
the model. The model: a bundle is a dict without zeros; `a op b` is per signal over the
union; `b op k` and `k op b` apply to the signals `b` has; comprehensions map each signal
of the domain; `//` and `%` truncate like Factorio; everything wraps at 32 bits.

usage: tools/fuzz_bundles.py [COUNT] [SEED]      (TICKY=./target/release/ticky)
"""
import os
import random
import subprocess
import sys
import tempfile

TICKY = os.environ.get("TICKY", "./target/release/ticky")
SIGNALS = ["iron-plate", "copper-plate", "coal", "stone", "signal-A", "signal-check"]


def wrap(v):
    return (v + 2**31) % 2**32 - 2**31


def tdiv(a, b):
    if b == 0:
        return 0
    q = abs(a) // abs(b)
    return wrap(q if (a >= 0) == (b >= 0) else -q)


def tmod(a, b):
    if b == 0:
        return 0
    return wrap(a - tdiv(a, b) * b)


def apply(op, a, b):
    return wrap({"+": lambda: a + b, "-": lambda: a - b, "*": lambda: a * b, "//": lambda: tdiv(a, b),
                 "%": lambda: tmod(a, b), "&": lambda: a & b, "|": lambda: a | b, "^": lambda: a ^ b}[op]())


def clean(d):
    return {s: v for s, v in d.items() if v != 0}


class Gen:
    """Builds an expression as (ticky source, python evaluator)."""

    def __init__(self, r):
        self.r = r

    def scalar(self):
        """A number not depending on `v`: (source, fn(env) -> int)."""
        k = self.r.random()
        if k < 0.4:
            c = self.r.randint(-6, 9)
            return str(c), lambda env, c=c: c
        if k < 0.7:
            return "x", lambda env: env["x"]
        op = self.r.choice(["+", "-", "*"])
        (sa, fa), (sb, fb) = self.scalar(), self.scalar()
        return f"({sa} {op} {sb})", lambda env: apply(op, fa(env), fb(env))

    def cond(self, depth=2):
        """A per-signal condition on `v`: (source, fn(env, v) -> bool)."""
        k = self.r.random()
        if depth == 0 or k < 0.6:
            cmp = self.r.choice(["<", ">", "==", "!=", "<=", ">="])
            ss, sf = self.scalar()
            ops = {"<": lambda a, b: a < b, ">": lambda a, b: a > b, "==": lambda a, b: a == b,
                   "!=": lambda a, b: a != b, "<=": lambda a, b: a <= b, ">=": lambda a, b: a >= b}
            f = ops[cmp]
            if self.r.random() < 0.5:
                return f"v {cmp} {ss}", lambda env, v: f(v, sf(env))
            return f"{ss} {cmp} v", lambda env, v: f(sf(env), v)
        if k < 0.85:
            op = self.r.choice(["and", "or"])
            (sa, fa), (sb, fb) = self.cond(depth - 1), self.cond(depth - 1)
            if op == "and":
                return f"({sa} and {sb})", lambda env, v: fa(env, v) and fb(env, v)
            return f"({sa} or {sb})", lambda env, v: fa(env, v) or fb(env, v)
        sa, fa = self.cond(depth - 1)
        return f"(not ({sa}))", lambda env, v: not fa(env, v)

    def value(self, depth=2):
        """A per-signal value of `v`: (source, fn(env, v) -> int)."""
        k = self.r.random()
        if depth == 0 or k < 0.3:
            if self.r.random() < 0.7:
                return "v", lambda env, v: v
            s, f = self.scalar()
            return s, lambda env, v: f(env)
        if k < 0.65:
            op = self.r.choice(["+", "-", "*", "//", "%", "&", "|", "^"])
            (sa, fa), (sb, fb) = self.value(depth - 1), self.value(depth - 1)
            return f"({sa} {op} {sb})", lambda env, v: apply(op, fa(env, v), fb(env, v))
        if k < 0.8:
            (sc, fc), (sa, fa), (sb, fb) = self.cond(1), self.value(depth - 1), self.value(depth - 1)
            return f"({sa} if {sc} else {sb})", lambda env, v: fa(env, v) if fc(env, v) else fb(env, v)
        if k < 0.9:
            fn = self.r.choice(["min", "max"])
            (sa, fa), (sb, fb) = self.value(depth - 1), self.scalar()
            pick = min if fn == "min" else max
            return f"{fn}({sa}, {sb})", lambda env, v: pick(fa(env, v), fb(env))
        sa, fa = self.value(depth - 1)
        return f"(-{sa})", lambda env, v: wrap(-fa(env, v))

    def bundle(self, depth=2):
        """A bundle: (source, fn(env) -> dict)."""
        k = self.r.random()
        if depth == 0 or k < 0.25:
            n = self.r.choice(["a", "b"])
            return n, lambda env: env[n]
        if k < 0.45:
            op = self.r.choice(["+", "-", "*", "//"])
            (sa, fa), (sb, fb) = self.bundle(depth - 1), self.bundle(depth - 1)

            def zip_(env):
                x, y = fa(env), fb(env)
                return clean({s: apply(op, x.get(s, 0), y.get(s, 0)) for s in set(x) | set(y)})
            return f"({sa} {op} {sb})", zip_
        if k < 0.6:
            op = self.r.choice(["+", "-", "*", "//", "%"])
            (sa, fa), (ss, sf) = self.bundle(depth - 1), self.scalar()
            if self.r.random() < 0.5 or op in ("//", "%"):
                return f"({sa} {op} {ss})", lambda env: clean({s: apply(op, v, sf(env)) for s, v in fa(env).items()})
            return f"({ss} {op} {sa})", lambda env: clean({s: apply(op, sf(env), v) for s, v in fa(env).items()})
        if k < 0.7:
            sig = self.r.sample(SIGNALS[:5], 2)
            (s1, f1), (s2, f2) = self.scalar(), self.scalar()
            src = f"Bundle({{\"{sig[0]}\": {s1}, \"{sig[1]}\": {s2}}})"
            return src, lambda env: clean({sig[0]: f1(env), sig[1]: f2(env)})
        sb, fb = self.bundle(depth - 1)
        sv, fv = self.value()
        conds = []
        if self.r.random() < 0.6:
            conds.append(self.cond())
        src = f"{{s: {sv} for s, v in {sb}.items()" + "".join(f" if {c[0]}" for c in conds) + "}"

        def comp(env):
            out = {}
            for s, v in fb(env).items():
                if all(c[1](env, v) for c in conds):
                    out[s] = fv(env, v)
            return clean(out)
        return src, comp


def rand_bundle(r):
    return clean({s: r.randint(-20, 30) for s in r.sample(SIGNALS, r.randint(0, 5))})


def fmt(b):
    return ",".join(f"{s}:{v}" for s, v in b.items()) or "{}"


def canon(b):
    return "{" + ",".join(f"{s}={v}" for s, v in sorted(b.items())) + "}"


def main():
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    r = random.Random(seed)
    failed = 0
    for i in range(count):
        g = Gen(r)
        src, f = g.bundle(3)
        shape = r.choice(["tick", "every", "main"])
        lines = ["input a: Bundle", "input b: Bundle", "input x: int @ X", "output o: Bundle", "output t: int @ T"]
        if shape == "tick":
            lines += ["every tick:", f"    o = {src}", "    t = len(o) * 1000 + o.total()"]
        elif shape == "every":
            lines += ["every 20 ticks:", f"    o = {src}", "    t = len(o) * 1000 + o.total()"]
        else:
            lines += ["while True:", f"    o = {src}", "    t = len(o) * 1000 + o.total()", "    wait 3"]
        env = {"a": rand_bundle(r), "b": rand_bundle(r), "x": r.randint(-9, 9)}
        want = f(env)
        want_t = wrap(len(want) * 1000 + wrap(sum(want.values())))
        with tempfile.NamedTemporaryFile("w", suffix=".ticky", delete=False) as fh:
            fh.write("\n".join(lines) + "\n")
            path = fh.name
        cmd = [TICKY, "sim", path, "--ticks", "200", f"--set=a={fmt(env['a'])}", f"--set=b={fmt(env['b'])}", f"--set=x={env['x']}"]
        out = subprocess.run(cmd, capture_output=True, text=True, check=False)
        if out.returncode != 0:
            failed += 1
            print(f"[{i + 1}/{count}] COMPILE FAILURE {path}:\n{out.stderr[-800:]}")
            continue
        last = out.stdout.strip().splitlines()[-1].split()
        got_o, got_t = last[1], int(last[2])
        # The simulator prints signals in table order; compare canonically.
        got = dict((p.split("=")[0], int(p.split("=")[1])) for p in got_o.strip("{}").split(",") if p)
        if canon(got) != canon(want) or got_t != want_t:
            failed += 1
            print(f"[{i + 1}/{count}] MISMATCH {path} ({shape}) env={env}\n  o = {src}\n  model {canon(want)} t={want_t}\n  ticky {canon(got)} t={got_t}")
        if (i + 1) % 25 == 0:
            print(f"[{i + 1}/{count}] {failed} failures so far", flush=True)
    print(f"{count} programs, {failed} failures")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()

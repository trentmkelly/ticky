#!/usr/bin/env python3
"""Fuzz selects with runtime arms (codegen picks, `selects::Out::Pick`) against Python.

Picks copy an arm value off the bus with one decider: `each` over a code table on red, the
arm conditions on green, the single output summing what passes. This fuzzer leans on what
that relies on: min/max/abs, ternaries and elif chains whose arms are inputs, shared values
and computed values; Python `%` and `//` by a runtime divisor (`r + (d if … else 0)`: the
remainder joins the pick as an always-on term); selects inside sums, scaled, compared and
feeding families of `+ k` lanes (straight-line packs); the same value in both arms; arms
equal to 0, INT_MIN and INT_MAX; inputs that are equal, zero (missing signals) or extreme.
Each program runs several input vectors in turn (`every N ticks` blocks or a main loop, the
emitters that pick; `every tick` blocks have their own emitter), sometimes `--opt=size`,
sometimes with picks off (`TICKY_NO_PICK=1`, to compare the old path on the same programs).
Overflowing or dividing-by-zero cases are left out, as in fuzz_exprs.py.

usage: tools/fuzz_selects.py [COUNT] [SEED]
"""
import json
import os
import random
import subprocess
import sys
import tempfile

from fuzz_exprs import Overflow, py_eval

TICKY = os.environ.get("TICKY", "./target/debug/ticky")
OUT_SIGNALS = "ABCDEFGHIJKLMNOPQRSTUVW"
INT_MIN, INT_MAX = -(2**31), 2**31 - 1
INPUTS = ["x", "y", "z", "w"]
SPACING = 150


def leaf(r):
    """An arm value: an input, a constant, or a small computed value (shared or not)."""
    c = r.random()
    if c < 0.55:
        return r.choice(INPUTS)
    if c < 0.7:
        return str(r.choice([0, 1, -1, 3, -7, 100, INT_MAX, INT_MIN + 1]))
    a, b = r.sample(INPUTS, 2)
    return r.choice([f"({a} + {b})", f"({a} - 1)", f"({a} * 3)", f"({a} ^ {b})", f"({a} & 255)"])


def cond(r, depth):
    a = leaf(r)
    b = r.choice([leaf(r), str(r.randint(-5, 5)), "0"])
    c = f"({a} {r.choice(['<', '<=', '>', '>=', '==', '!='])} {b})"
    if depth > 0 and r.random() < 0.3:
        c = f"({c} {r.choice(['and', 'or'])} {cond(r, depth - 1)})"
    if r.random() < 0.1:
        c = f"(not {c})"
    return c


def sel(r, depth):
    """A select with runtime arms."""
    a, b = leaf(r), leaf(r)
    c = r.random()
    if depth > 0 and r.random() < 0.3:
        a = sel(r, depth - 1)
    if c < 0.18:
        return f"min({a}, {b})"
    if c < 0.36:
        return f"max({a}, {b})"
    if c < 0.44:
        # Parenthesised so py_eval range-checks the result (abs(INT_MIN) overflows).
        return f"(abs({a}))"
    if c < 0.5:
        return f"({a} if {cond(r, 1)} else {a})"
    if c < 0.62:
        return f"({a} % {b})"
    if c < 0.68:
        return f"({a} // {b})"
    if c < 0.8 and depth > 0:
        return f"({a} if {cond(r, 1)} else ({b} if {cond(r, 1)} else {sel(r, depth - 1)}))"
    return f"({a} if {cond(r, 1)} else {b})"


def use(r, e):
    """Uses a select in more logic: sums (picked addends), scales, comparisons, lanes."""
    v = r.choice(INPUTS)
    return r.choice([
        e, e, e,
        f"({e} + {v})", f"({v} + {e})", f"({e} - {v})", f"({v} - {e})",
        f"({e} * 2)", f"({e} + 5)", f"(({e} + {v}) + 1)",
        f"({e} > {v})", f"(1 if {e} > 0 else 2)",
        f"({e} ^ {v})", f"({e} & 4095)",
    ])


def vector(r):
    vals = [0, 0, 1, -1, 2, -2, 7, -7, 100, INT_MIN, INT_MAX, INT_MIN + 1, INT_MAX - 1]
    env = {}
    for v in INPUTS:
        env[v] = r.choice(vals) if r.random() < 0.6 else r.randint(-40, 40)
    if r.random() < 0.3:
        a, b = r.sample(INPUTS, 2)
        env[b] = env[a]
    return env


def state_at(lines, tick):
    """The outputs as of `tick`, from `ticky sim`'s change lines."""
    cur = None
    for line in lines[1:]:
        f = line.split()
        if int(f[0]) <= tick:
            cur = f[1:]
    return cur


def main():  # pylint: disable=too-many-locals,too-many-statements,too-many-branches
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    r = random.Random(seed)
    tested = failed = picked = 0
    for rnd in range(count):
        exprs = []
        for _ in range(r.randint(4, len(OUT_SIGNALS))):
            exprs.append(use(r, sel(r, r.randint(0, 2))))
        # Families of `+ k` on selects next to each other: straight-line packs over picks.
        if r.random() < 0.3:
            k = r.choice([3, -5, 1000])
            for _ in range(r.randint(2, 4)):
                exprs.append(f"(({sel(r, 0)} + {k}) ^ {r.choice(INPUTS)})")
        exprs = exprs[: len(OUT_SIGNALS)]
        envs = [vector(r) for _ in range(r.randint(2, 5))]
        # Keep the expressions defined (no overflow, no division by zero) on every vector.
        cases = []
        for e in exprs:
            try:
                cases.append((e, [py_eval(e, env) for env in envs]))
            except (Overflow, ZeroDivisionError, ValueError, TypeError):
                pass
        if not cases:
            continue
        lines = [f"input {v}: int @ {v.upper()}" for v in INPUTS]
        lines += [f"output o{i}: int @ {OUT_SIGNALS[i]}" for i in range(len(cases))]
        main_loop = r.random() < 0.35
        lines.append("while True:" if main_loop else f"every {r.choice([12, 20, 30])} ticks:")
        lines += [f"    o{i} = {e}" for i, (e, _) in enumerate(cases)]
        if main_loop:
            lines.append("    wait 1")
        opt = ["--opt=size"] if r.random() < 0.3 else []
        env_extra = {"TICKY_NO_PICK": "1"} if r.random() < 0.1 else {}
        with tempfile.NamedTemporaryFile("w", suffix=".ticky", delete=False) as f:
            f.write("\n".join(lines) + "\n")
            path = f.name
        sets = []
        for i, env in enumerate(envs):
            sets += [f"--set={k}={v}@{i * SPACING}" for k, v in env.items()]
        cmd = [TICKY, "sim", path, "--ticks", str(len(envs) * SPACING)] + sets + opt
        out = subprocess.run(cmd, capture_output=True, text=True, check=False, env=dict(os.environ, **env_extra))
        if out.returncode != 0:
            print(f"round {rnd}: compile failed ({path})\n{out.stderr}")
            failed += 1
            continue
        sim_lines = out.stdout.strip().splitlines()
        bad = False
        for vi, env in enumerate(envs):
            got = state_at(sim_lines, (vi + 1) * SPACING - 1)
            for i, (e, wants) in enumerate(cases):
                tested += 1
                if got is None or int(got[i]) != wants[vi]:
                    failed += 1
                    bad = True
                    print(f"MISMATCH (seed {seed}, round {rnd}, vector {vi}) {env} {' '.join(opt)} {env_extra}\n"
                          f"  o{i} = {e}\n  python {wants[vi]}, ticky {None if got is None else got[i]}")
        bp = subprocess.run([TICKY, "build", path, "--json"] + opt, capture_output=True, text=True, check=False,
                            env=dict(os.environ, **env_extra))
        if bp.returncode == 0 and "off the bus)" in json.dumps(json.loads(bp.stdout)):
            picked += 1
        if bad:
            print(f"  program kept: {path}")
        else:
            os.unlink(path)
    print(f"{count} programs ({picked} with picks), {tested} outputs checked, {failed} mismatches")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()

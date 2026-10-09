#!/usr/bin/env python3
"""Fuzz Ticky's expression semantics against Python itself.

Generates random integer expressions over inputs x, y, z, evaluates them with Python (skipping
any that overflow 32 bits or divide by zero, where Ticky deliberately differs), compiles them
into `every tick:` outputs and checks the simulated results.

usage: tools/fuzz_exprs.py [ROUNDS] [SEED]
"""
import os
import random
import re
import subprocess
import sys
import tempfile

TICKY = os.environ.get("TICKY", "./target/debug/ticky")
INT_MIN, INT_MAX = -(2**31), 2**31 - 1
OUT_SIGNALS = "ABCDEFGHIJKLMNOPQRSTUVW"


class Overflow(Exception):
    """A value left the 32-bit range, where Ticky wraps but Python doesn't."""


def check(v):
    """`v` as an int, if it fits in 32 bits."""
    v = int(v)
    if not INT_MIN <= v <= INT_MAX:
        raise Overflow
    return v


def gen(depth, r):  # pylint: disable=too-many-return-statements
    """A random expression of at most `depth` levels."""
    if depth == 0 or r.random() < 0.25:
        leaves = ["x", "y", "z", str(r.randint(-9, 9)), str(r.randint(0, 40)), "True", "False"]
        return r.choice(leaves)
    kind = r.random()

    def a():
        return gen(depth - 1, r)
    if kind < 0.35:
        op = r.choice(["+", "-", "*", "//", "%", "&", "|", "^"])
        return f"({a()} {op} {a()})"
    if kind < 0.42:
        return f"({a()} {r.choice(['<<', '>>'])} {r.randint(0, 4)})"
    if kind < 0.6:
        op = r.choice(["<", "<=", ">", ">=", "==", "!="])
        if r.random() < 0.2:
            return f"({a()} {op} {a()} {r.choice(['<', '<='])} {a()})"
        return f"({a()} {op} {a()})"
    if kind < 0.72:
        return f"({a()} {r.choice(['and', 'or'])} {a()})"
    if kind < 0.77:
        return f"(not {a()})"
    if kind < 0.87:
        return f"({a()} if {a()} else {a()})"
    if kind < 0.9:
        return f"(-{a()})"
    if kind < 0.92:
        return f"(~{a()})"
    if kind < 0.95:
        return f"abs({a()})"
    return f"{r.choice(['min', 'max'])}({a()}, {a()})"


def py_eval(expr, env):
    """Evaluates with Python semantics, failing on any intermediate outside 32 bits."""
    # Wrap every parenthesised subexpression's result in a range check.
    checked = re.sub(r"(?<![A-Za-z_])\(", "_c(", expr)
    scope = {"_c": check, "abs": abs, "min": min, "max": max}
    return check(eval(checked, scope, dict(env)))  # pylint: disable=eval-used


def main():  # pylint: disable=too-many-locals
    """Runs the fuzzer."""
    rounds = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    r = random.Random(seed)
    tested = failed = 0
    for rnd in range(rounds):
        env = {"x": r.randint(-30, 30), "y": r.randint(-30, 30), "z": r.randint(-5, 5)}
        cases = []
        while len(cases) < len(OUT_SIGNALS):
            e = gen(r.randint(1, 4), r)
            try:
                cases.append((e, py_eval(e, env)))
            except (Overflow, ZeroDivisionError, ValueError, TypeError):
                pass
        lines = ["input x: int @ X", "input y: int @ Y", "input z: int @ Z"]
        lines += [f"output o{i}: int @ {OUT_SIGNALS[i]}" for i in range(len(cases))]
        lines.append("every tick:")
        lines += [f"    o{i} = {e}" for i, (e, _) in enumerate(cases)]
        with tempfile.NamedTemporaryFile("w", suffix=".ticky", delete=False) as f:
            f.write("\n".join(lines) + "\n")
            path = f.name
        sets = [f"--set={k}={v}" for k, v in env.items()]
        cmd = [TICKY, "sim", path, "--ticks", "200"] + sets
        out = subprocess.run(cmd, capture_output=True, text=True, check=False)
        if out.returncode != 0:
            print(f"round {rnd}: compile failed\n{out.stderr}")
            failed += 1
            continue
        last = out.stdout.strip().splitlines()[-1].split()[1:]
        for i, (e, want) in enumerate(cases):
            tested += 1
            if int(last[i]) != want:
                failed += 1
                print(f"MISMATCH (seed {seed}, round {rnd}) "
                      f"x={env['x']} y={env['y']} z={env['z']}\n  {e}\n  python {want}, ticky {last[i]}")
    print(f"{tested} expressions, {failed} mismatches")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()

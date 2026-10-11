#!/usr/bin/env python3
"""Fuzz range comprehensions (`[f(k, x, y) for k in range(…)]`) against Python.

Element expressions mix the range variable with inputs and constants (`+ - * // %`, floor
division by constants of both signs and by inputs, comparisons, `x if c else y`, `min`,
`max`, `abs`), so some are vectorised into bundle operations and some stay unrolled. The
array is read by constant and runtime indexes, summed, sorted, sometimes written element by
element, in the main program or an `every` block. Final outputs are compared with Python.

usage: tools/fuzz_comps.py [COUNT] [SEED]
"""
import os
import random
import re
import subprocess
import sys
import tempfile

TICKY = os.environ.get("TICKY", "./target/debug/ticky")
INT_MIN, INT_MAX = -(2**31), 2**31 - 1


class Overflow(Exception):
    """A value left the 32-bit range, where Ticky wraps but Python doesn't."""


def check(v):
    """`v` as an int, if it fits in 32 bits."""
    v = int(v)
    if not INT_MIN <= v <= INT_MAX:
        raise Overflow
    return v


def expr(r, depth, arith=False):  # pylint: disable=too-many-return-statements
    """A random element expression of `k`, `x` and `y` (`arith`: mostly arithmetic)."""
    if depth == 0 or r.random() < 0.25:
        return r.choice(["k", "k", "x", "y", str(r.randint(-9, 9)), r.choice(["100", "-1000"])])

    def a():
        return expr(r, depth - 1, arith)

    p = r.random() * (0.6 if arith else 1) + (0.4 if arith and r.random() < 0.1 else 0)
    if p < 0.35:
        return f"({a()} {r.choice(['+', '-', '*', '&', '|', '^'])} {a()})"
    if p < 0.6:
        d = r.choice(["x", "y"] + [str(c) for c in [-41, -7, -3, -2, -1, 1, 2, 3, 5, 10, 41, 1000]])
        return f"({a()} {r.choice(['//', '%'])} {d})"
    if p < 0.72:
        return f"({a()} {r.choice(['<', '>', '==', '!=', '<=', '>='])} {a()})"
    if p < 0.85:
        return f"({a()} if {a()} {r.choice(['<', '>', '=='])} {a()} else {a()})"
    if p < 0.95:
        return f"{r.choice(['min', 'max'])}({a()}, {a()})"
    return f"abs({a()})"


def program(r):
    """(Ticky source lines, Python source lines, output expressions)."""
    start = r.randint(-5, 5)
    step = r.choice([1, 1, 1, 2, 3, -1, -2])
    n = r.randint(2, 20)
    stop = start + step * n
    rng = f"range({n})" if start == 0 and step == 1 else f"range({start}, {stop}, {step})"
    if r.random() < 0.3:
        # Sorting's shape: `(k * s + t) % c - d`, with `s`, `t` inputs or constants.
        def v():
            return r.choice(["x", "y", str(r.randint(-50, 50))])

        c = r.choice([-41, -10, -3, 2, 3, 7, 41, 1000])
        elt = f"((k * {v()} + {v()}) {r.choice(['%', '//'])} {c}) {r.choice(['+', '-', '*'])} {v()}"
    else:
        elt = expr(r, r.randint(1, 4), r.random() < 0.6)
    comp = f"ys = [{elt} for k in {rng}]"
    outs = ["sum(ys)", f"ys[{r.randint(0, n - 1)}]", f"ys[{r.randint(-n, -1)}]", "len(ys)"]
    body = [comp]
    if r.random() < 0.4:
        outs.append("ys[i % len(ys)]")
    if r.random() < 0.4:
        body.append(f"zs = sorted(ys{', reverse=True' if r.random() < 0.5 else ''})")
        outs.append(f"zs[{r.randint(0, n - 1)}]")
    if r.random() < 0.2:
        body.append(f"ys[{r.randint(0, n - 1)}] = x")
    if r.random() < 0.3:
        body.append(f"ws = [{expr(r, 2, True)} for k in range({r.randint(2, 6)})]")
        outs.append("sum(ws)")
    return body, outs[:7]


def run_python(x, y, i, body, outs):
    """The outputs under Python semantics, or None on overflow/division by zero."""
    checked = [re.sub(r"(?<![A-Za-z_0-9])\(", "_c(", line) for line in body]
    env = {"_c": check, "x": x, "y": y, "i": i}
    try:
        for line in checked:
            exec(line, env)  # pylint: disable=exec-used
        for v in env.get("ys", []) + env.get("ws", []):
            check(v)
        return tuple(check(eval(o, env)) for o in outs)  # pylint: disable=eval-used
    except (Overflow, ZeroDivisionError):
        return None


def main():  # pylint: disable=too-many-locals
    """Runs the fuzzer."""
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    r = random.Random(seed)
    tested = failed = 0
    while tested < count:
        body, outs = program(r)
        x, y, i = r.randint(-30, 30), r.randint(-30, 30), r.randint(0, 50)
        want = run_python(x, y, i, body, outs)
        if want is None:
            continue
        tested += 1
        names = "ABCEFGH"
        lines = ["input x: int @ X", "input y: int @ Y", "input i: int @ I"]
        lines += [f"output o{j}: int @ {names[j]}" for j in range(len(outs))]
        lines.append("output done: bool @ D")
        if r.random() < 0.5:
            lines += body + [f"o{j} = {o}" for j, o in enumerate(outs)] + ["done = True"]
        else:
            lines += ["every 60 ticks:"] + ["    " + s for s in body]
            lines += [f"    o{j} = {o}" for j, o in enumerate(outs)] + ["    done = True"]
        with tempfile.NamedTemporaryFile("w", suffix=".ticky", delete=False) as f:
            f.write("\n".join(lines) + "\n")
            path = f.name
        cmd = [TICKY, "sim", path, "--ticks", "400", f"--set=x={x}", f"--set=y={y}", f"--set=i={i}"]
        out = subprocess.run(cmd, capture_output=True, text=True, check=False)
        if out.returncode != 0:
            failed += 1
            print(f"COMPILE FAILURE ({path}):\n{out.stderr[-1500:]}")
            continue
        last = [int(v) for v in out.stdout.strip().splitlines()[-1].split()[1:]]
        got = tuple(last[: len(outs)])
        if got != want or last[len(outs)] != 1:
            failed += 1
            done = last[len(outs)]
            print(f"MISMATCH ({path}) x={x} y={y} i={i}: python {want}, ticky {got} done={done}")
        else:
            os.unlink(path)
    print(f"{tested} programs, {failed} failures")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()

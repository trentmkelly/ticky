#!/usr/bin/env python3
"""Fuzz element ranges of state arrays and bundles against Python.

A state array (and sometimes a bundle) is updated for K rounds by maps over its elements
(`xs = [min(t + 40, 600) for t in xs]`, clamps, offsets, `//`/`%` by constants, selects,
random expressions), element writes by constant and runtime indexes (zeros included), and
dict comprehensions on the bundle, in an `every N ticks` block or a loop in the main
program. The compiler bounds the elements from the initial values and these updates (a
fixpoint), so these shapes check that the bounds (and what they fold) are right: values that
leave a bound, zeros on slots, wrapping, negative numbers. Final outputs are compared with
Python.

usage: tools/fuzz_elemranges.py [COUNT] [SEED]
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


def small(r):
    return r.choice([0, 1, 2, 3, 5, 7, 10, 40, 100, 560, 600, -1, -3, -40, -600])


def elt(r, v, depth=2, floors=True):
    """A random element expression of `v` (and inputs `x`, `y`), mostly range-shaped."""
    a, b = small(r), small(r)
    lo, hi = sorted([small(r), small(r)])
    shapes = [
        f"min(({v} + {a}), {b})",
        f"max(({v} - {a}), {b})",
        f"min(max(({v} + {a}), {lo}), {hi})",
        f"(({v} + {a}) if ({v} < {b}) else {b})",
        f"({a} if ({v} > {b}) else ({v} + {a}))",
        f"(abs({v}) - {a})",
        f"(({v} + x) if ({v} >= {b}) else y)",
        f"(({v} * {r.choice([2, 3, -2, 1000])}) + {a})",
    ]
    if floors:
        d = r.choice([2, 3, 7, 10, -3, 600])
        c1, c2 = r.choice([10, 1000]), r.choice([10, 100, 10000])
        shapes += [f"(({v} + {a}) % {d})", f"(({v} // {d}) + {a})", f"(({v} * {c1}) // {c2})"]
    if depth > 0 and r.random() < 0.3:
        return elt(r, elt(r, v, depth - 1, floors), depth - 1, floors)
    if r.random() < 0.15:
        ops = ["+", "-", "*", "&", "|", "^", "<", ">", "=="]
        return f"(({v} {r.choice(ops)} {r.choice(['x', 'y', str(a)])}) {r.choice(['+', '-'])} {b})"
    return r.choice(shapes)


def program(r):
    """(state lines, body lines, outputs, rounds) as Ticky source; Python mirrors it."""
    n = r.randint(2, 8)
    init = [r.choice([0, 0, small(r), r.randint(-50, 50)]) for _ in range(n)]
    if r.random() < 0.4:
        init = [init[0]] * n
    state = [f"xs = {init}"]
    body = []
    bundle = r.random() < 0.35
    if bundle:
        state.append(f'b = {{"iron-plate": {small(r)}, "copper-plate": {small(r)}, "stone": 0}}')
    for _ in range(r.randint(1, 4)):
        p = r.random()
        if p < 0.45:
            body.append(f"xs = [{elt(r, 't')} for t in xs]")
        elif p < 0.6:
            body.append(f"xs[{r.randint(0, n - 1)}] = {r.choice(['x', 'y', '0', str(small(r))])}")
        elif p < 0.75:
            val = r.choice(["x", "0", str(small(r)), "xs[0] + 1"])
            body.append(f"xs[(n + {r.randint(0, 3)}) % {n}] = {val}")
        elif p < 0.85:
            body.append(f"if x > {r.randint(-20, 20)}:")
            body.append(f"    xs[n % {n}] = {r.choice(['0', 'y', str(small(r))])}")
        elif bundle:
            # Bundle comprehensions truncate `//` and `%`: leave them out.
            body.append(f"b = {{s: {elt(r, 'v', 1, False)} for s, v in b.items()}}")
        else:
            body.append(f"xs = [{elt(r, 't')} for t in xs]")
    if bundle and r.random() < 0.5:
        body.append('b["stone"] = xs[0]')
    outs = [f"xs[{k}]" for k in range(min(n, 4))] + ["sum(xs)", f"xs[n % {n}]"]
    outs.append(f"(1 if xs[{r.randint(0, n - 1)}] > {small(r)} else 0)")
    if bundle:
        outs += ['b["iron-plate"]', 'b["copper-plate"]', 'b["stone"]']
    return state, body, outs[:9], r.randint(1, 6)


def run_python(x, y, prog):
    """The outputs under Python semantics, or None on overflow/division by zero."""
    state, body, outs, rounds = prog
    env = {"_c": check, "x": x, "y": y, "n": 0}
    for line in state:
        exec(line, env)  # pylint: disable=exec-used
    # A bundle has no zero signals, so a comprehension skips them.
    body = [line.replace("in b.items()}", "in b.items() if v != 0}") for line in body]
    code = "\n".join(re.sub(r"(?<![A-Za-z_0-9])\(", "_c(", line) for line in body)
    try:
        for _ in range(rounds):
            exec(code, env)  # pylint: disable=exec-used
            env["xs"] = [check(v) for v in env["xs"]]
            if "b" in env:
                env["b"] = {s: check(v) for s, v in env["b"].items() if v != 0}
            env["n"] += 1
        env["b"] = _Missing0(env.get("b", {}))
        return tuple(check(eval(o, env)) for o in outs)  # pylint: disable=eval-used
    except (Overflow, ZeroDivisionError):
        return None


class _Missing0(dict):
    """A bundle: missing signals read 0."""

    def __missing__(self, key):
        return 0


def main():  # pylint: disable=too-many-locals
    """Runs the fuzzer."""
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    r = random.Random(seed)
    tested = failed = 0
    while tested < count:
        prog = program(r)
        state, body, outs, rounds = prog
        x, y = r.choice([r.randint(-30, 30), 0, 600, -600, 2**31 - 1]), r.randint(-30, 30)
        want = run_python(x, y, prog)
        if want is None:
            continue
        tested += 1
        names = "ABCEFGHJK"
        lines = ["input x: int @ X", "input y: int @ Y"]
        lines += [f"output o{j}: int @ {names[j]}" for j in range(len(outs))]
        lines.append("output done: bool @ D")
        lines += state + ["n = 0"]
        if r.random() < 0.6:
            lines += [f"every {r.choice([40, 60])} ticks:", f"    if n < {rounds}:"]
            lines += ["        " + s for s in body] + ["        n += 1"]
            lines += [f"    o{j} = {o}" for j, o in enumerate(outs)] + [f"    done = n == {rounds}"]
            ticks = 60 * rounds + 300
        else:
            lines += [f"while n < {rounds}:"] + ["    " + s for s in body] + ["    n += 1"]
            lines += [f"o{j} = {o}" for j, o in enumerate(outs)] + ["done = True"]
            ticks = 400 * rounds + 400
        with tempfile.NamedTemporaryFile("w", suffix=".ticky", delete=False) as f:
            f.write("\n".join(lines) + "\n")
            path = f.name
        cmd = [TICKY, "sim", path, "--ticks", str(ticks), f"--set=x={x}", f"--set=y={y}"]
        out = subprocess.run(cmd, capture_output=True, text=True, check=False)
        if out.returncode != 0:
            if "too much branching" in out.stderr or "ran out of signals" in out.stderr:
                tested -= 1
                os.unlink(path)
                continue
            failed += 1
            print(f"COMPILE FAILURE ({path}):\n{out.stderr[-1500:]}")
            continue
        last = [int(v) for v in out.stdout.strip().splitlines()[-1].split()[1:]]
        got = tuple(last[: len(outs)])
        if got != want or last[len(outs)] != 1:
            failed += 1
            done = last[len(outs)]
            print(f"MISMATCH ({path}) x={x} y={y}: python {want}, ticky {got} done={done}")
        else:
            os.unlink(path)
    print(f"{tested} programs, {failed} failures")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Fuzz the timing of pipelined `every tick:` blocks against Python, with inputs that change
every few ticks (the other fuzzers hold inputs still, so a value from the wrong iteration
would go unnoticed there).

Each random block has outputs computed from the inputs x, y, z alone (combinational) and,
in half of the programs, state a, b, c updated from them plus an iteration counter n. The
simulated trace must match Python tick for tick for one alignment: iteration k reads the
inputs of tick base + k, and every output of an iteration appears together.

usage: tools/fuzz_pipes.py [COUNT] [SEED]
"""
import os
import random
import re
import subprocess
import sys
import tempfile
import textwrap

from fuzz_exprs import gen, Overflow, check
from fuzz_blocks import straight
from fuzz_programs import Gen, VARS

TICKY = os.environ.get("TICKY", "./target/debug/ticky")
TICKS = 160
SCOPE = {"_c": check, "abs": abs, "min": min, "max": max}


def inputs(r):
    """Per-tick values of x, y, z, and the --set flags that produce them."""
    vals = {k: [] for k in "xyz"}
    sets = []
    for k in "xyz":
        v = r.randint(-9, 9)
        for t in range(TICKS):
            if t == 0 or r.random() < 0.4:
                v = r.randint(-30, 30) if k != "z" else r.randint(-5, 5)
                sets.append(f"--set={k}={v}@{t}")
            vals[k].append(v)
    return vals, sets


def compiled(src, name):
    """`src` with every parenthesis checked for overflow, compiled for exec/eval."""
    checked = re.sub(r"(?<![A-Za-z_0-9])\(", "_c(", src)
    return compile(checked, name, "exec" if "\n" in src else "eval")


def at(vals, t):
    """The inputs at tick t."""
    return {k: vals[k][t] for k in "xyz"}


def replay(vals, body, inits, base):
    """States after 0, 1, 2, … iterations, iteration k reading the inputs of tick base + k."""
    code = compiled(textwrap.dedent("\n".join(body)) + "\n", "<block>")
    env = dict(SCOPE, **inits)
    states = [tuple(inits[v] for v in VARS)]
    for t in range(base + 1, TICKS):
        if t >= 0:
            env.update(at(vals, t))
            exec(code, env)  # pylint: disable=exec-used
            states.append(tuple(check(env[v]) for v in VARS))
    return states


def matches(rows, vals, block):
    """Whether some alignment makes the trace agree with Python (None: Python overflowed)."""
    body, inits, exprs = block
    try:
        want = [[eval(e, SCOPE, at(vals, t)) for e in exprs] for t in range(TICKS)]  # pylint: disable=eval-used
    except (Overflow, ZeroDivisionError):
        return None
    ncomb = len(exprs)
    if not body:
        # The outputs at tick t are from the inputs of tick t - lat.
        return any(all(rows[t][:ncomb] == want[t - lat] for t in range(lat + 1, TICKS))
                   for lat in range(40))
    for base in range(0, 40):
        try:
            states = replay(vals, body, inits, base)
        except (Overflow, ZeroDivisionError):
            return None
        shown = [row for row in rows if row[-1] > 0]
        if any(row[-1] >= len(states) or tuple(row[ncomb:ncomb + 3]) != states[row[-1]]
               for row in shown):
            continue
        # The combinational outputs show the inputs of the iteration whose state shows
        # (give or take a tick: they may be read a tick before the commit).
        for d in (-1, 0, 1):
            ticks = [(row, base + row[-1] + d) for row in shown if 0 <= base + row[-1] + d < TICKS]
            if all(row[:ncomb] == want[t] for row, t in ticks):
                return True
    return False


def main():  # pylint: disable=too-many-locals
    """Runs the fuzzer."""
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    r = random.Random(seed)
    tested = failed = skipped = 0
    while tested < count:
        stateful = r.random() < 0.5
        exprs = [gen(r.randint(1, 4), r) for _ in range(r.randint(1, 4))]
        lines = ["input x: int @ X", "input y: int @ Y", "input z: int @ Z"]
        lines += [f"output e{i}: int @ {'EFGH'[i]}" for i in range(len(exprs))]
        body, inits = [], {}
        if stateful:
            body = straight(Gen(r), "    ", 2, r.randint(1, 4))
            inits = {v: r.randint(-5, 5) for v in VARS}
            lines += [f"output o{v}: int @ {v.upper()}" for v in VARS] + ["output on: int @ N"]
            lines += [f"{v} = {k}" for v, k in inits.items()] + ["n = 0"]
        lines.append("every tick:")
        lines += [f"    e{i} = {e}" for i, e in enumerate(exprs)]
        if stateful:
            lines += ["    n += 1"] + body + [f"    o{v} = {v}" for v in VARS] + ["    on = n"]
        with tempfile.NamedTemporaryFile("w", suffix=".ticky", delete=False) as f:
            f.write("\n".join(lines) + "\n")
            path = f.name
        vals, sets = inputs(r)
        report = subprocess.run([TICKY, "check", path], capture_output=True, text=True, check=False)
        if "pipelined" not in report.stdout + report.stderr:
            # Multi-cycle (state feeds back through logic): not what this fuzzer is about.
            skipped += 1
            os.unlink(path)
            continue
        cmd = [TICKY, "sim", path, "--all", "--ticks", str(TICKS)] + sets
        out = subprocess.run(cmd, capture_output=True, text=True, check=False)
        if out.returncode != 0:
            failed += 1
            tested += 1
            print(f"COMPILE FAILURE ({path}):\n{out.stderr}")
            continue
        rows = [[int(v) for v in line.split()[1:]] for line in out.stdout.strip().splitlines()[1:]]
        ok = matches(rows, vals, (body, inits, [compiled(e, "<expr>") for e in exprs]))
        if ok is None:
            skipped += 1
            continue
        tested += 1
        if not ok:
            failed += 1
            print(f"MISMATCH ({path})")
            with open(path + ".sets", "w", encoding="utf-8") as f:
                f.write(" ".join(sets) + "\n")
        else:
            os.unlink(path)
    print(f"{tested} blocks, {failed} failures ({skipped} skipped: overflow or not pipelined)")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()

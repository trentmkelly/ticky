#!/usr/bin/env python3
"""Fuzz stateful `every tick:` blocks against Python.

Each random block updates variables a, b, c from inputs x, y and also counts its own
iterations in n. Outputs are glitch-free, so the last observed (a, b, c, n) is a consistent
snapshot: Python replays exactly n iterations and must reach the same values.

usage: tools/fuzz_blocks.py [COUNT] [SEED]
"""
import os
import random
import subprocess
import sys
import tempfile
import textwrap

from fuzz_programs import Gen, check, checked, Overflow, VARS

TICKY = os.environ.get("TICKY", "./target/debug/ticky")


def straight(g, ind, depth, n):
    """Statements without loops: assignments, aug-assignments and if/elif/else."""
    out = []
    for _ in range(n):
        k = g.r.random()
        v = g.r.choice(VARS)
        if depth == 0 or k < 0.6:
            if g.r.random() < 0.4:
                out.append(f"{ind}{v} {g.r.choice(['+=', '-='])} {g.expr(1)}")
            else:
                out.append(f"{ind}{v} = {g.expr()}")
        else:
            out.append(f"{ind}if {g.cond()}:")
            out += straight(g, ind + "    ", depth - 1, g.r.randint(1, 2))
            if g.r.random() < 0.3:
                out.append(f"{ind}elif {g.cond()}:")
                out += straight(g, ind + "    ", depth - 1, 1)
            if g.r.random() < 0.5:
                out.append(f"{ind}else:")
                out += straight(g, ind + "    ", depth - 1, g.r.randint(1, 2))
    return out


def replay(body, x, y, inits, n):
    """(a, b, c) after n iterations under Python semantics, or None on overflow."""
    src = textwrap.dedent("\n".join(checked(line) for line in body))
    code = compile(src, "<block>", "exec")
    env = {"_c": check, "min": min, "max": max, "x": x, "y": y}
    env.update(inits)
    try:
        for _ in range(n):
            exec(code, env)  # pylint: disable=exec-used
            for v in VARS:
                check(env[v])
        return tuple(env[v] for v in VARS)
    except (Overflow, ZeroDivisionError):
        return None


def main():  # pylint: disable=too-many-locals
    """Runs the fuzzer."""
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    r = random.Random(seed)
    tested = failed = skipped = 0
    while tested < count:
        g = Gen(r)
        body = straight(g, "    ", 2, r.randint(1, 4))
        x, y = r.randint(-9, 9), r.randint(-9, 9)
        inits = {v: r.randint(-5, 5) for v in VARS}
        ticks = r.choice([40, 120, 300])
        lines = ["input x: int @ X", "input y: int @ Y"]
        lines += [f"output o{v}: int @ {v.upper()}" for v in VARS] + ["output on: int @ N"]
        lines += [f"{v} = {k}" for v, k in inits.items()] + ["n = 0", "every tick:", "    n += 1"]
        lines += body + [f"    o{v} = {v}" for v in VARS] + ["    on = n"]
        with tempfile.NamedTemporaryFile("w", suffix=".ticky", delete=False) as f:
            f.write("\n".join(lines) + "\n")
            path = f.name
        cmd = [TICKY, "sim", path, "--ticks", str(ticks), f"--set=x={x}", f"--set=y={y}"]
        out = subprocess.run(cmd, capture_output=True, text=True, check=False)
        if out.returncode != 0:
            failed += 1
            tested += 1
            print(f"COMPILE FAILURE ({path}):\n{out.stderr}")
            continue
        last = [int(v) for v in out.stdout.strip().splitlines()[-1].split()[1:]]
        want = replay(body, x, y, inits, last[3])
        if want is None:
            skipped += 1
            continue
        tested += 1
        if tuple(last[:3]) != want:
            failed += 1
            print(f"MISMATCH ({path}) x={x} y={y} after {last[3]} iterations: "
                  f"python {want}, ticky {tuple(last[:3])}")
    print(f"{tested} blocks, {failed} failures ({skipped} skipped for overflow)")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()

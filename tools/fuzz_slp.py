#!/usr/bin/env python3
"""Fuzz straight-line vectorisation (fuse/slp.rs) against Python.

Each program computes families of parallel, same-shape operations: lanes `f_i op k` (or
`k op f_i`, or `f_i cmp k`) over small single-use expressions `f_i` of inputs x, y, z (some
array reads), with one constant per family or a different one per lane, each lane's result
consumed by more logic (so it isn't just an output register's load). Some lanes feed other
lanes, some inputs are shared (not packable), and inputs are often 0 so lanes see missing
signals. Blocks are `every N ticks:` or a main-program loop: the emitters that pack. Results
are checked after the values settle; cases that overflow 32 bits or divide by zero are left
out, as in fuzz_exprs.py. Reports how many programs had packs.

usage: tools/fuzz_slp.py [COUNT] [SEED]
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
AR_OPS = ["+", "-", "*", "//", "%", "&", "|", "^", "<<", ">>"]
CMP_OPS = ["<", "<=", ">", ">=", "==", "!="]


def base(r, table):
    """A small expression of the inputs that is its own combinator (or an array read)."""
    a, b, c = r.sample(["x", "y", "z"], 3)  # distinct, so nothing folds to a constant or an input
    k = r.choice([-9, -5, -2, 2, 3, 7])
    forms = [
        lambda: f"({a} ^ {b})",
        lambda: f"({a} + {b})",
        lambda: f"({a} - {b})",
        lambda: f"({a} & {b})",
        lambda: f"({a} * {k})",
        lambda: f"max({a}, {k})",
        lambda: f"({a} if {b} > {k} else {c})",
        lambda: f"({a} > {b})",
        lambda: f"abs({a})",
    ]
    if table:
        forms.append(lambda: f"T[({a} & 7)]")
    return r.choice(forms)()


def constant(r, op):
    """A constant that keeps a lane in range: small shifts, nonzero divisors."""
    if op in ("<<", ">>"):
        return r.randint(0, 5)
    if op in ("//", "%"):
        return r.choice([-7, -3, -2, 2, 3, 4, 8, 16])
    return r.choice([-100, -9, -3, -1, 1, 2, 3, 5, 7, 12, 255, 1000])


def lane(r, fam, i, table):
    """Lane i of family `fam` = (kind, op, constants)."""
    kind, op, ks = fam
    k = ks[i % len(ks)]
    f = base(r, table)
    if kind == "left":
        return f"({k} {op} {f})"
    return f"({f} {op} {k})"


def consume(r, e, fams, table):
    """Uses lane result `e` in more logic (sometimes another family's lane)."""
    v = r.choice(["x", "y", "z"])
    c = r.random()
    if c < 0.15 and fams:
        kind, op, ks = r.choice(fams)
        k = r.choice(ks)
        return f"(({k} {op} {e}) ^ {v})" if kind == "left" else f"(({e} {op} {k}) ^ {v})"
    if c < 0.25 and table:
        return f"T[({e} & 7)]"
    if c < 0.3:
        return e
    # Mostly operations that read the lane from where it is (a select would gate it instead).
    return r.choice([f"({e} ^ {v})", f"({e} ^ {v})", f"({e} & 4095)", f"({e} | {v})", f"max({e}, {v})", f"min({e}, {r.randint(-50, 50)})"])


def program(r):
    """A random program: its source lines and the output expressions."""
    table = [r.randint(-20, 20) for _ in range(8)] if r.random() < 0.5 else None
    fams = []
    for _ in range(r.randint(1, 3)):
        kind = r.choice(["right", "right", "left", "cmp"])
        op = r.choice(CMP_OPS if kind == "cmp" else AR_OPS)
        n = 1 if r.random() < 0.6 else r.randint(2, 4)
        fams.append((kind, op, [constant(r, op) for _ in range(n)]))
    exprs = []
    for fam in fams:
        for i in range(r.randint(2, 6)):
            exprs.append(consume(r, lane(r, fam, i, table), fams, table))
    # A shared input: not packable, but next to packs.
    if r.random() < 0.4:
        f = base(r, table)
        exprs.append(f"({f} * 3)")
        exprs.append(f"({f} ^ 5)")
    return table, exprs[: len(OUT_SIGNALS)]


def main():  # pylint: disable=too-many-locals,too-many-statements
    """Runs the fuzzer."""
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    r = random.Random(seed)
    tested = failed = packed = 0
    for rnd in range(count):
        table, exprs = program(r)
        env = {v: r.choice([0, 0, r.randint(-30, 30)]) for v in "xyz"}
        scope = dict(env)
        if table:
            scope["T"] = table
        cases = []
        for e in exprs:
            try:
                cases.append((e, py_eval(e, scope)))
            except (Overflow, ZeroDivisionError, ValueError, TypeError, IndexError):
                pass
        if not cases:
            continue
        lines = ["input x: int @ X", "input y: int @ Y", "input z: int @ Z"]
        lines += [f"output o{i}: int @ {OUT_SIGNALS[i]}" for i in range(len(cases))]
        if table:
            lines.append(f"T = {table}")
        main_loop = r.random() < 0.4
        lines.append("while True:" if main_loop else "every 60 ticks:")
        lines += [f"    o{i} = {e}" for i, (e, _) in enumerate(cases)]
        if main_loop:
            lines.append("    wait 1")
        opt = ["--opt=size"] if r.random() < 0.3 else []
        with tempfile.NamedTemporaryFile("w", suffix=".ticky", delete=False) as f:
            f.write("\n".join(lines) + "\n")
            path = f.name
        sets = [f"--set={k}={v}" for k, v in env.items()]
        out = subprocess.run([TICKY, "sim", path, "--ticks", "400"] + sets + opt, capture_output=True, text=True, check=False)
        if out.returncode != 0:
            print(f"round {rnd}: compile failed ({path})\n{out.stderr}")
            failed += 1
            continue
        last = out.stdout.strip().splitlines()[-1].split()[1:]
        bad = False
        for i, (e, want) in enumerate(cases):
            tested += 1
            if int(last[i]) != want:
                failed += 1
                bad = True
                print(f"MISMATCH (seed {seed}, round {rnd}) x={env['x']} y={env['y']} z={env['z']} {' '.join(opt)}\n"
                      f"  o{i} = {e}\n  python {want}, ticky {last[i]}")
        bp = subprocess.run([TICKY, "build", path, "--json"] + opt, capture_output=True, text=True, check=False)
        if bp.returncode == 0 and "lanes at once" in json.dumps(json.loads(bp.stdout)):
            packed += 1
        if bad:
            print(f"  program kept: {path}")
        else:
            os.unlink(path)
    print(f"{count} programs ({packed} with packs), {tested} outputs, {failed} mismatches")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()

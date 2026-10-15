#!/usr/bin/env python3
"""Fuzz Ticky's processes (SPEC §9.2, §9.6) against Python.

Each program has 2–3 sequential processes (the last one is sometimes `main`), each a random
program from fuzz_programs over its own local variables a, b, c. Process k > 0 first waits
for process k-1's flag and reads its result `r{k-1}` as `z`, the "write the data, then set
the flag" pattern. Python runs the bodies one after another; the final values must match.

Most bodies end with a loop whose iterations have independent work feeding a recurrence of
dependence distance 0–3 (`pipe_loop`: counting up or down, `while` loops, nested in another
loop), the shape loop pipelining (crate::modsched) transforms. It comes from a separate random
stream, so the rest of each program is the same as before it was added.

With PGO=1 (tools/fuzz_pgo.py) the circuit is built with a profile recorded by
`ticky test --profile` (as in fuzz_programs.py).

usage: tools/fuzz_procs.py [COUNT] [SEED]
"""
import os
import random
import subprocess
import sys
import tempfile

sys.path.insert(0, os.path.dirname(__file__))
from fuzz_programs import Gen, run_python  # pylint: disable=wrong-import-position

TICKY = os.environ.get("TICKY", "./target/debug/ticky")
PGO = bool(os.environ.get("PGO"))


def pipe_loop(r2, tag, has_z):
    """Lines of a loop whose iterations have work that doesn't depend on earlier ones (an
    expression of the loop index and values fixed before the loop) feeding a recurrence of
    dependence distance 1, 2 or 3 (or none), folded into `c` at the end. Values stay small,
    so the program can't overflow where it didn't before. Overlapping iterations
    (crate::modsched) computes the independent work an iteration early."""
    i, q = f"pi{tag}", f"pq{tag}"
    leaves = [i, i, q, str(r2.randint(-4, 9))] + ([f"pz{tag}"] if has_z else [])

    def expr(depth):
        if depth == 0 or r2.random() < 0.2:
            return r2.choice(leaves)
        op = r2.choice(["+", "-", "*", "*", "%"])
        if op == "%":
            return f"({expr(depth - 1)} % {r2.randint(2, 13)})"
        return f"({expr(depth - 1)} {op} {expr(depth - 1)})"

    f = f"({expr(r2.randint(2, 3))} % 1009)"
    s, u, v, w = (f"p{x}{tag}" for x in "suvw")
    lines = [f"{q} = b % 13", f"{s} = 0", f"{u} = 1", f"{v} = 2", f"{w} = 3"]
    if has_z:
        lines.append(f"pz{tag} = z % 97")
    update = r2.choice([
        f"{s} = {f}",                                   # no recurrence but the index
        f"{s} = ({s} * 2 + {f}) % 1009",                # distance 1
        f"{u}, {v} = {v}, ({u} + {f}) % 1009",          # distance 2
        f"{u}, {v}, {w} = {v}, {w}, ({u} * 3 + {f}) % 1009",  # distance 3
    ])
    n, lo = r2.randint(0, 9), r2.randint(-3, 3)
    if r2.random() < 0.25:
        # A `while` loop counting first.
        lines += [f"{i} = {lo}", f"while {i} < {lo + n}:", f"    {i} += 1", f"    {update}"]
    else:
        step = r2.choice([1, 1, 1, 2, 3, -1, -2])
        rng = f"range({lo}, {lo + n}, {step})" if step > 0 else f"range({lo + n}, {lo}, {step})"
        lines += [f"for {i} in {rng}:", f"    {update}"]
        if r2.random() < 0.3:
            lines.insert(lines.index(f"for {i} in {rng}:") + 2, f"    {w} = ({w} + {s}) % 1009")
    if r2.random() < 0.25:
        # Inside another loop: the loop is entered again and again.
        k = lines.index(next(x for x in lines if x.startswith(("for ", f"{i} = "))))
        lines = lines[:k] + [f"for po{tag} in range(2):"] + ["    " + x for x in lines[k:]]
    lines.append(f"c = c ^ ({s} + {u} * 7 + {v} * 3 + {w})")
    return lines


class ZGen(Gen):
    """Programs that may also read `z` (the previous process's result)."""

    def __init__(self, r, has_z):
        super().__init__(r)
        self.has_z = has_z

    def leaf(self):
        if self.has_z and self.r.random() < 0.15:
            return "z"
        return super().leaf()


def main():  # pylint: disable=too-many-locals
    """Runs the fuzzer."""
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    r = random.Random(seed)
    # Pipelinable loops (pipe_loop) come from their own stream: the rest of each program is
    # what it was before they were added.
    r2 = random.Random(seed * 1000003 + 7)
    tested = failed = 0
    while tested < count:
        n = r.randint(2, 3)
        x, y = r.randint(-20, 20), r.randint(-20, 20)
        bodies, wants, z = [], [], 0
        for k in range(n):
            body = ZGen(r, k > 0).block("", 3, r.randint(2, 5))
            if r2.random() < 0.6:
                body += pipe_loop(r2, k, k > 0)
            want = run_python([f"z = {z}"] + body, x, y)
            if want is None:
                break
            bodies.append(body)
            wants.append(want)
            z = want[0]
        if len(bodies) < n:
            continue
        tested += 1
        lines = ["input x: int @ X", "input y: int @ Y"]
        sigs = iter("ABCEFGHIJKLMNOPQ")
        for k in range(n):
            lines += [f"output o{k}{v}: int @ {next(sigs)}" for v in "abc"]
        lines += [f"r{k} = 0" for k in range(n)] + [f"f{k} = False" for k in range(n)]
        main_last = r.random() < 0.5
        for k, body in enumerate(bodies):
            is_main = main_last and k == n - 1
            ind = "" if is_main else "    "
            if not is_main:
                lines.append(f"process p{k}:")
            pre = ["a = 0", "b = 1", "c = 2"]
            if k > 0:
                pre = [f"wait until f{k - 1}", f"z = r{k - 1}"] + pre
            post = [f"o{k}{v} = {v}" for v in "abc"] + [f"r{k} = a", f"f{k} = True"]
            lines += [ind + line for line in pre + body + post]
        if PGO:
            px, py = (x, y) if r.random() < 0.5 else (r.randint(-20, 20), r.randint(-20, 20))
            lines += ['test "profile":', f"    set x = {px}", f"    set y = {py}", "    run 30000 ticks"]
        src = "\n".join(lines) + "\n"
        with tempfile.NamedTemporaryFile("w", suffix=".ticky", delete=False) as f:
            f.write(src)
            path = f.name
        cmd = [TICKY, "sim", path, "--ticks", "30000", f"--set=x={x}", f"--set=y={y}"]
        if PGO:
            prof = path + ".profile.json"
            rec = subprocess.run([TICKY, "test", path, "--profile", prof], capture_output=True, text=True, check=False)
            if not os.path.exists(prof):
                failed += 1
                print(f"PROFILE FAILURE ({path}):\n{rec.stderr}")
                continue
            cmd += ["--profile", prof]
        out = subprocess.run(cmd, capture_output=True, text=True, check=False)
        if out.returncode != 0:
            failed += 1
            print(f"COMPILE FAILURE ({path}):\n{out.stderr}")
            continue
        last = [int(v) for v in out.stdout.strip().splitlines()[-1].split()[1:]]
        got = [tuple(last[3 * k:3 * k + 3]) for k in range(n)]
        if got != wants:
            failed += 1
            print(f"MISMATCH ({path}) x={x} y={y}: python {wants}, ticky {got}")
    print(f"{tested} programs, {failed} failures")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()

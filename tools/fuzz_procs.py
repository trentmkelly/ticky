#!/usr/bin/env python3
"""Fuzz Ticky's processes (SPEC §9.2, §9.6) against Python.

Each program has 2–3 sequential processes (the last one is sometimes `main`), each a random
program from fuzz_programs over its own local variables a, b, c. Process k > 0 first waits
for process k-1's flag and reads its result `r{k-1}` as `z`, the "write the data, then set
the flag" pattern. Python runs the bodies one after another; the final values must match.

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
    tested = failed = 0
    while tested < count:
        n = r.randint(2, 3)
        x, y = r.randint(-20, 20), r.randint(-20, 20)
        bodies, wants, z = [], [], 0
        for k in range(n):
            body = ZGen(r, k > 0).block("", 3, r.randint(2, 5))
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
        src = "\n".join(lines) + "\n"
        with tempfile.NamedTemporaryFile("w", suffix=".ticky", delete=False) as f:
            f.write(src)
            path = f.name
        cmd = [TICKY, "sim", path, "--ticks", "30000", f"--set=x={x}", f"--set=y={y}"]
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

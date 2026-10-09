#!/usr/bin/env python3
"""Fuzz Ticky's sequential semantics against Python itself.

Generates random programs (assignments, if/elif/else, for, while, break, continue) over
variables a, b, c and inputs x, y; runs them with Python's exec (skipping programs where any
value leaves 32 bits or divides by zero) and with the compiled circuit in the simulator, and
compares the final values.

usage: tools/fuzz_programs.py [COUNT] [SEED]
"""
import os
import random
import re
import subprocess
import sys
import tempfile

TICKY = os.environ.get("TICKY", "./target/debug/ticky")
INT_MIN, INT_MAX = -(2**31), 2**31 - 1
VARS = ["a", "b", "c"]


class Overflow(Exception):
    """A value left the 32-bit range, where Ticky wraps but Python doesn't."""


def check(v):
    """`v` as an int, if it fits in 32 bits."""
    v = int(v)
    if not INT_MIN <= v <= INT_MAX:
        raise Overflow
    return v


class Gen:
    """Random program generator."""

    def __init__(self, r):
        self.r = r
        self.scope = []  # loop variables visible here
        self.loops = 0
        self.n = 0

    def leaf(self):
        """A variable, input, loop variable or small constant."""
        opts = VARS + ["x", "y"] + self.scope + [str(self.r.randint(-5, 9))]
        return self.r.choice(opts)

    def expr(self, depth=2):
        """A random expression."""
        if depth == 0 or self.r.random() < 0.3:
            return self.leaf()
        k = self.r.random()
        if k < 0.5:
            op = self.r.choice(["+", "-", "*", "//", "%", "&", "^"])
            return f"({self.expr(depth - 1)} {op} {self.expr(depth - 1)})"
        if k < 0.75:
            op = self.r.choice(["<", ">", "==", "!=", "<=", ">="])
            return f"({self.expr(depth - 1)} {op} {self.expr(depth - 1)})"
        if k < 0.85:
            return f"({self.expr(depth - 1)} if {self.cond()} else {self.expr(depth - 1)})"
        return f"{self.r.choice(['min', 'max'])}({self.expr(depth - 1)}, {self.expr(depth - 1)})"

    def cond(self):
        """A random condition."""
        c = f"({self.expr(1)} {self.r.choice(['<', '>', '==', '!=', '<=', '>='])} {self.expr(1)})"
        if self.r.random() < 0.3:
            c = f"({c} {self.r.choice(['and', 'or'])} ({self.expr(1)} > {self.expr(1)}))"
        if self.r.random() < 0.15:
            c = f"(not {c})"
        return c

    def block(self, ind, depth, n):
        """`n` statements at indentation `ind`."""
        out = []
        for _ in range(n):
            out += self.stmt(ind, depth)
        return out or [ind + "pass"]

    def stmt(self, ind, depth):  # pylint: disable=too-many-return-statements
        """One random statement (as source lines)."""
        k = self.r.random()
        v = self.r.choice(VARS)
        if depth == 0 or k < 0.4:
            if self.r.random() < 0.3:
                return [f"{ind}{v} {self.r.choice(['+=', '-=', '*='])} {self.expr(1)}"]
            if self.r.random() < 0.15:
                w = self.r.choice(VARS)
                return [f"{ind}{v}, {w} = {self.expr(1)}, {self.expr(1)}"]
            return [f"{ind}{v} = {self.expr()}"]
        if k < 0.6:
            lines = [f"{ind}if {self.cond()}:"] + self.block(ind + "    ", depth - 1, self.r.randint(1, 3))
            if self.r.random() < 0.4:
                lines += [f"{ind}elif {self.cond()}:"] + self.block(ind + "    ", depth - 1, self.r.randint(1, 2))
            if self.r.random() < 0.5:
                lines += [f"{ind}else:"] + self.block(ind + "    ", depth - 1, self.r.randint(1, 2))
            return lines
        if k < 0.75 and self.loops < 2:
            self.n += 1
            i = f"i{self.n}"
            bound = self.r.choice([str(self.r.randint(0, 5)), "x % 4", f"{self.r.randint(-2, 2)}, y % 5"])
            self.scope.append(i)
            self.loops += 1
            body = self.block(ind + "    ", depth - 1, self.r.randint(1, 3))
            body += self.flow(ind + "    ")
            self.loops -= 1
            self.scope.pop()
            return [f"{ind}for {i} in range({bound}):"] + body
        if k < 0.85 and self.loops < 2:
            self.n += 1
            w = f"w{self.n}"
            self.loops += 1
            body = [f"{ind}    {w} += 1"] + self.block(ind + "    ", depth - 1, self.r.randint(1, 3)) + self.flow(ind + "    ")
            self.loops -= 1
            extra = f" and {self.cond()}" if self.r.random() < 0.5 else ""
            return [f"{ind}{w} = 0", f"{ind}while {w} < {self.r.randint(1, 5)}{extra}:"] + body
        return [f"{ind}{v} = {self.expr()}"]

    def flow(self, ind):
        """Maybe a conditional break/continue at the end of a loop body."""
        if self.r.random() < 0.4:
            return [f"{ind}if {self.cond()}:", f"{ind}    {self.r.choice(['break', 'continue'])}"]
        return []


def run_python(body, x, y):
    """Final (a, b, c) under Python semantics, or None if the program leaves 32 bits."""
    src = "\n".join(re.sub(r"(?<![A-Za-z_0-9])\(", "_c(", line) for line in body)
    env = {"_c": check, "min": min, "max": max, "x": x, "y": y, "a": 0, "b": 1, "c": 2}
    try:
        exec(src, env)  # pylint: disable=exec-used
        return tuple(check(env[v]) for v in VARS)
    except (Overflow, ZeroDivisionError):
        return None


def main():  # pylint: disable=too-many-locals
    """Runs the fuzzer."""
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    r = random.Random(seed)
    tested = failed = 0
    while tested < count:
        g = Gen(r)
        body = g.block("", 3, r.randint(2, 6))
        x, y = r.randint(-20, 20), r.randint(-20, 20)
        want = run_python(body, x, y)
        if want is None:
            continue
        tested += 1
        lines = ["input x: int @ X", "input y: int @ Y", "output oa: int @ A", "output ob: int @ B",
                 "output oc: int @ C", "output done: bool @ D", "a = 0", "b = 1", "c = 2"]
        lines += body + ["oa = a", "ob = b", "oc = c", "done = True"]
        src = "\n".join(lines) + "\n"
        with tempfile.NamedTemporaryFile("w", suffix=".ticky", delete=False) as f:
            f.write(src)
            path = f.name
        cmd = [TICKY, "sim", path, "--ticks", "20000", f"--set=x={x}", f"--set=y={y}"]
        out = subprocess.run(cmd, capture_output=True, text=True, check=False)
        if out.returncode != 0:
            failed += 1
            print(f"COMPILE FAILURE ({path}):\n{out.stderr}")
            continue
        last = [int(v) for v in out.stdout.strip().splitlines()[-1].split()[1:]]
        got = tuple(last[:3])
        if last[3] != 1 or got != want:
            failed += 1
            print(f"MISMATCH ({path}) x={x} y={y}: python {want}, ticky {got} done={last[3]}")
    print(f"{tested} programs, {failed} failures")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Fuzz functions and arrays against Python.

Random programs define a few functions (parameters, locals, loops, early returns), use an
array with constant and runtime indexes, assign tuples of variables and elements (swaps and
rotations, indexes from loop variables), and call the functions from expressions (including
inside `and`/`or`/conditional expressions, where Python short-circuits). Some programs run as
one `every` block instead of the main program. Final values are compared with Python's own
execution.

usage: tools/fuzz_level2.py [COUNT] [SEED]
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


class Gen:  # pylint: disable=too-many-instance-attributes
    """Random program generator with functions and an array."""

    def __init__(self, r):
        self.r = r
        self.funcs = []          # (name, arity) callable from here
        self.readable = []       # scalar names readable here
        self.assignable = []     # scalar names assignable here
        self.loops = 0
        self.n = 0

    def leaf(self):
        """A variable, constant, array element or call."""
        k = self.r.random()
        if k < 0.12:
            return f"arr[{self.expr(1)} % 4]"
        if k < 0.17:
            return f"arr[{self.r.randint(-4, 3)}]"
        if k < 0.2:
            return self.r.choice(["sum(arr)", "max(arr)", "min(arr)", "len(arr)"])
        if k < 0.32 and self.funcs:
            name, arity = self.r.choice(self.funcs)
            return f"{name}({', '.join(self.expr(1) for _ in range(arity))})"
        return self.r.choice(self.readable + [str(self.r.randint(-5, 9))])

    def expr(self, depth=2):
        """A random expression."""
        if depth == 0 or self.r.random() < 0.3:
            return self.leaf()
        k = self.r.random()
        a = lambda: self.expr(depth - 1)  # noqa: E731
        if k < 0.45:
            return f"({a()} {self.r.choice(['+', '-', '*', '//', '%', '&', '^'])} {a()})"
        if k < 0.65:
            return f"({a()} {self.r.choice(['<', '>', '==', '!=', '<=', '>='])} {a()})"
        if k < 0.8:
            return f"({a()} {self.r.choice(['and', 'or'])} {a()})"
        if k < 0.92:
            return f"({a()} if {a()} else {a()})"
        return f"{self.r.choice(['min', 'max'])}({a()}, {a()})"

    def stmt(self, ind, depth):
        """One statement (as source lines)."""
        k = self.r.random()
        if depth == 0 or k < 0.45:
            if self.r.random() < 0.12:
                return [f"{ind}{self.tuple_assign()}"]
            if self.r.random() < 0.2:
                return [f"{ind}arr[{self.expr(1)} % 4] = {self.expr()}"]
            v = self.r.choice(self.assignable)
            if self.r.random() < 0.3:
                return [f"{ind}{v} {self.r.choice(['+=', '-='])} {self.expr(1)}"]
            return [f"{ind}{v} = {self.expr()}"]
        if k < 0.7:
            lines = [f"{ind}if {self.expr(1)}:"] + self.block(ind + "    ", depth - 1)
            if self.r.random() < 0.5:
                lines += [f"{ind}else:"] + self.block(ind + "    ", depth - 1)
            return lines
        if self.loops < 2:
            self.n += 1
            i = f"i{self.n}"
            self.loops += 1
            self.readable.append(i)
            body = self.block(ind + "    ", depth - 1)
            if self.r.random() < 0.3:
                body += [f"{ind}    if {self.expr(1)}:", f"{ind}        {self.r.choice(['break', 'continue'])}"]
            self.readable.remove(i)
            self.loops -= 1
            return [f"{ind}for {i} in range({self.r.randint(0, 4)}):"] + body
        return [f"{ind}{self.r.choice(self.assignable)} = {self.expr()}"]

    def index(self):
        """An index into `arr`: constant, from a loop variable, or any expression."""
        loop_vars = [v for v in self.readable if v.startswith("i")]
        k = self.r.random()
        if k < 0.4 and loop_vars:
            return f"({self.r.choice(loop_vars)} + {self.r.randint(0, 3)}) % 4"
        if k < 0.6:
            return str(self.r.randint(-4, 3))
        return f"{self.expr(1)} % 4"

    def tuple_assign(self):
        """`t1, t2[, t3] = …` over scalars and array elements, often a swap or rotation."""
        targets = []
        for _ in range(self.r.choice([2, 2, 3])):
            if self.r.random() < 0.6:
                targets.append(f"arr[{self.index()}]")
            else:
                targets.append(self.r.choice(self.assignable))
        if self.r.random() < 0.6:
            values = targets[1:] + targets[:1]
            values = [v if self.r.random() < 0.8 else self.expr(1) for v in values]
        else:
            values = [self.expr(1) for _ in targets]
        return f"{', '.join(targets)} = {', '.join(values)}"

    def block(self, ind, depth):
        """A few statements."""
        out = []
        for _ in range(self.r.randint(1, 3)):
            out += self.stmt(ind, depth)
        return out

    def function(self, name):
        """A random function definition (source lines) taking two parameters."""
        saved = (self.readable, self.assignable)
        self.readable, self.assignable = ["p", "q", "r"], ["p", "q", "r"]
        lines = [f"def {name}(p, q):", "    r = 0"]
        lines += self.block("    ", 2)
        if self.r.random() < 0.5:
            lines += [f"    if {self.expr(1)}:", f"        return {self.expr()}"]
        lines += self.block("    ", 1)
        lines.append(f"    return {self.expr()}")
        self.readable, self.assignable = saved
        return lines


def run_python(src):
    """Final (a, b, c, arr) under Python semantics, or None on overflow/division by zero."""
    checked = "\n".join(re.sub(r"(?<![A-Za-z_0-9])\(", "_c(", line) for line in src)
    env = {"_c": check}
    try:
        exec(checked, env)  # pylint: disable=exec-used
        return tuple(check(env[v]) for v in ["a", "b", "c"]) + tuple(check(v) for v in env["arr"])
    except (Overflow, ZeroDivisionError, RecursionError):
        return None


def main():  # pylint: disable=too-many-locals
    """Runs the fuzzer."""
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    r = random.Random(seed)
    tested = failed = 0
    while tested < count:
        g = Gen(r)
        x, y = r.randint(-20, 20), r.randint(-20, 20)
        src = ["arr = [3, -1, 4, 1]", "a = 0", "b = 1", "c = 2"]
        every = r.random() < 0.3
        # Functions see their parameters, locals and the module's variables. (Not in `every`
        # programs: inlined into unrolled loops, they make circuits too big to test quickly.)
        for k in range(0 if every else r.randint(1, 3)):
            src += g.function(f"f{k}")
            g.funcs.append((f"f{k}", 2))
        g.readable, g.assignable = ["a", "b", "c", "x", "y"], ["a", "b", "c"]
        body = []
        for _ in range(r.randint(2, 5)):
            body += g.stmt("", 3)
        py = [f"x = {x}", f"y = {y}"] + src + body
        want = run_python(py)
        if want is None:
            continue
        tested += 1
        lines = ["input x: int @ X", "input y: int @ Y"]
        lines += [f"output o{i}: int @ {s}" for i, s in enumerate("ABCEFGH")] + ["output done: bool @ D"]
        outs = [f"o{i} = {v}" for i, v in enumerate(["a", "b", "c", "arr[0]", "arr[1]", "arr[2]", "arr[3]"])]
        if every:
            # The same program as one `every` block (loops unroll, so loop-variable indexes
            # become constants): it starts from the initial values on every run.
            lines += ["every 1000 ticks:"] + ["    " + l for l in src + body + outs + ["done = True"]]
        else:
            lines += src + body + outs + ["done = True"]
        with tempfile.NamedTemporaryFile("w", suffix=".ticky", delete=False) as f:
            f.write("\n".join(lines) + "\n")
            path = f.name
        cmd = [TICKY, "sim", path, "--ticks", "30000", f"--set=x={x}", f"--set=y={y}"]
        out = subprocess.run(cmd, capture_output=True, text=True, check=False)
        if out.returncode != 0 and every and "too much branching" in out.stderr:
            tested -= 1  # an `every` block's limit on unrolled `break`s, not a bug
            continue
        if out.returncode != 0:
            failed += 1
            print(f"COMPILE FAILURE ({path}):\n{out.stderr[-1500:]}")
            continue
        last = [int(v) for v in out.stdout.strip().splitlines()[-1].split()[1:]]
        if tuple(last[:7]) != want or last[7] != 1:
            failed += 1
            print(f"MISMATCH ({path}) x={x} y={y}: python {want}, ticky {tuple(last[:7])} done={last[7]}")
    print(f"{tested} programs, {failed} failures")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()

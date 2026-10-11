#!/usr/bin/env python3
"""Fuzz sorting networks and min/max trees (order statistics) against Python.

Random programs sort a few inputs with an unrolled network (bubble sort as a function with
`if xs[j] > xs[j + 1]:` swaps, random compare-and-swap networks written with `min`/`max` or
with swaps, median-of-3 formulas) or compute a random tree of `min`/`max`, and output some
of the results. Leaves are the inputs, values computed from them, constants, or the slots
of a state array. Each program runs a test block that sets many input vectors (duplicates,
zeros, negatives, INT_MIN/INT_MAX) and checks every output against Python.

usage: tools/fuzz_sortnets.py [COUNT] [SEED]
"""
import os
import random
import re
import subprocess
import sys
import tempfile

TICKY = os.environ.get("TICKY", "./target/debug/ticky")
INT_MIN, INT_MAX = -(2**31), 2**31 - 1
IN_SIGNALS = "ABCDEFGHIJKLMNOP"
OUT_SIGNALS = "QRSTUVWXYZ"


def wrap(v):
    """`v` wrapped to 32 bits, as Factorio does."""
    return (v + 2**31) % 2**32 - 2**31


def value(r, pool):
    """A random input value: often a repeat, zero, ±1 or an end of the range."""
    k = r.random()
    if k < 0.25 and pool:
        return r.choice(pool)
    if k < 0.4:
        return 0
    if k < 0.5:
        return r.choice([INT_MIN, INT_MAX, INT_MIN + 1, INT_MAX - 1, 1, -1])
    if k < 0.8:
        return r.randint(-9, 9)
    return r.randint(INT_MIN, INT_MAX)


class Gen:  # pylint: disable=too-many-instance-attributes
    """A random program: its source and a Python model of its outputs."""

    def __init__(self, r):
        self.r = r
        self.n = r.choice([3, 3, 4, 5, 5, 6, 7, 8, 8, 9, 12, 16])
        # How the leaves are made from the inputs: (ticky expression, python function).
        self.leaves = []
        sign = r.random()
        for i in range(self.n):
            k = r.random()
            if sign < 0.1:  # never negative (one selector)
                self.leaves.append((f"(x{i} & 1023)", lambda e, i=i: e[i] & 1023))
            elif sign < 0.2:  # never positive
                self.leaves.append((f"(-(x{i} & 1023))", lambda e, i=i: -(e[i] & 1023)))
            elif k < 0.6:
                self.leaves.append((f"x{i}", lambda e, i=i: e[i]))
            elif k < 0.75:
                c = r.randint(-3, 3)
                self.leaves.append((f"(x{i} + {c})", lambda e, i=i, c=c: wrap(e[i] + c)))
            elif k < 0.85:
                self.leaves.append((f"(x{i} * 3)", lambda e, i=i: wrap(e[i] * 3)))
            else:
                c = r.choice([0, 0, 1, -1, r.randint(-9, 9), INT_MIN, INT_MAX])
                self.leaves.append((str(c), lambda e, c=c: c))
        self.state_array = r.random() < 0.4
        # The main program (as a loop) too, for small networks: its `if`s are branches.
        blocks = ["every tick:", "every 120 ticks:"] + (["while True:"] if self.n <= 5 else [])
        self.block = r.choice(blocks)
        self.body = []
        self.funcs = []
        self.outs = []  # (ticky expression, python function of the leaf values)
        r.choice([self.bubble, self.network, self.network, self.tree, self.median3])()

    # ---------------------------------------------------------------- shapes

    def bubble(self):
        """A bubble sort function, unrolled by the compiler; strict or non-strict swap, by a
        temporary, a tuple assignment or `min`/`max`."""
        op = self.r.choice([">", ">", ">="])
        a, b = "xs[j]", "xs[j + 1]"
        swap = self.r.choice([
            [f"            if {a} {op} {b}:", f"                t = {a}",
             f"                {a} = {b}", f"                {b} = t"],
            [f"            if {a} {op} {b}:", f"                {a}, {b} = {b}, {a}"],
            [f"            {a}, {b} = min({a}, {b}), max({a}, {b})"],
        ])
        self.funcs += [
            "def sort(xs):",
            f"    for i in range({self.n} - 1):",
            f"        for j in range({self.n} - 1 - i):",
            *swap,
            "    return xs",
        ]
        self.body.append("    ys = sort(vs)")
        self.pick_outputs("ys", sorted)

    def network(self):
        """Random compare-and-swaps (in either direction), written as min/max or as swaps."""
        steps = []
        for _ in range(self.r.randint(self.n, self.n * self.n // 2 + 2)):
            i, j = self.r.sample(range(self.n), 2)
            steps.append((i, j))
        for i, j in steps:
            a, b = f"vs[{i}]", f"vs[{j}]"
            k = self.r.random()
            if k < 0.4:
                self.body.append(f"    {a}, {b} = min({a}, {b}), max({a}, {b})")
            elif k < 0.7:
                self.body += [f"    if {a} > {b}:", f"        {a}, {b} = {b}, {a}"]
            elif k < 0.85:
                self.body += [f"    if {b} < {a}:", f"        t = {a}", f"        {a} = {b}",
                              f"        {b} = t"]
            else:
                self.body += [f"    lo = {a} if {a} <= {b} else {b}",
                              f"    hi = {b} if {a} <= {b} else {a}",
                              f"    {a} = lo", f"    {b} = hi"]

        def run(vals):
            v = list(vals)
            for i, j in steps:
                if v[i] > v[j]:
                    v[i], v[j] = v[j], v[i]
            return v
        self.pick_outputs("vs", run)

    def tree(self):
        """Random nested min/max over the leaves (often not an order statistic)."""
        def gen(ixs):
            if len(ixs) == 1:
                return f"vs[{ixs[0]}]", lambda v, i=ixs[0]: v[i]
            cut = self.r.randint(1, len(ixs) - 1)
            (ea, fa), (eb, fb) = gen(ixs[:cut]), gen(ixs[cut:])
            f = self.r.choice(["min", "max"])
            py = min if f == "min" else max
            return f"{f}({ea}, {eb})", lambda v, fa=fa, fb=fb, py=py: py(fa(v), fb(v))
        for _ in range(self.r.randint(1, 4)):
            ixs = list(range(self.n))
            self.r.shuffle(ixs)
            ixs = ixs[:self.r.randint(3, self.n)]
            e, f = gen(ixs)
            self.outs.append((e, f))
        # min/max of all, written as one call
        f = self.r.choice(["min", "max"])
        args = ", ".join(f"vs[{i}]" for i in range(self.n))
        self.outs.append((f"{f}({args})", min if f == "min" else max))

    def median3(self):
        """Median of three by formula, over the first three leaves; and the others' min."""
        def med(v):
            return sorted(v[:3])[1]
        self.outs.append(("max(min(vs[0], vs[1]), min(max(vs[0], vs[1]), vs[2]))", med))
        self.outs.append(("min(max(vs[0], vs[1]), max(vs[1], vs[2]), max(vs[0], vs[2]))", med))
        self.tree()

    def pick_outputs(self, name, model):
        """Outputs some positions of the sorted array `name` (`model` sorts in Python)."""
        ks = sorted(self.r.sample(range(self.n), self.r.randint(1, min(self.n, 4))))
        for k in ks:
            self.outs.append((f"{name}[{k}]", lambda v, k=k: model(v)[k]))

    # ---------------------------------------------------------------- program

    def source(self, vectors):
        """The program, with a test block checking `vectors`."""
        outs = self.outs[:len(OUT_SIGNALS)]
        lines = [f"input x{i}: int @ {IN_SIGNALS[i]}" for i in range(self.n)]
        lines += [f"output o{i}: int @ {OUT_SIGNALS[i]}" for i in range(len(outs))]
        if self.state_array:
            lines.append(f"vs = [0] * {self.n}")
        lines += self.funcs
        lines.append(self.block)
        if self.state_array:
            lines += [f"    vs[{i}] = {e}" for i, (e, _) in enumerate(self.leaves)]
        else:
            lines.append(f"    vs = [{', '.join(e for e, _ in self.leaves)}]")
        lines += self.body
        lines += [f"    o{i} = {e}" for i, (e, _) in enumerate(outs)]
        lines.append('test "network":')
        for env in vectors:
            leaves = [f(env) for _, f in self.leaves]
            for i, x in enumerate(env):
                lines.append(f"    set x{i} = {x}")
            lines.append(f"    run {800 if self.block == 'while True:' else 250} ticks")
            for i, (_, f) in enumerate(outs):
                lines.append(f"    assert o{i} == {f(leaves)}")
        return "\n".join(lines) + "\n"


def main():  # pylint: disable=too-many-locals
    """Runs the fuzzer."""
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 20
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    r = random.Random(seed)
    failed = programs = skipped = 0
    for p in range(count):
        g = Gen(r)
        vectors = []
        for _ in range(10):
            pool = []
            env = []
            for _ in range(g.n):
                x = value(r, pool)
                pool.append(x)
                env.append(x)
            vectors.append(env)
        src = g.source(vectors)
        with tempfile.NamedTemporaryFile("w", suffix=".ticky", delete=False) as f:
            f.write(src)
            path = f.name
        out = subprocess.run([TICKY, "test", path], capture_output=True, text=True, check=False)
        text = out.stdout + out.stderr
        if "ran out of signals" in text or "ticks per iteration, but asks for" in text:
            skipped += 1  # too big for the signal allocation or too deep for the period
            os.unlink(path)
            continue
        programs += 1
        if out.returncode != 0 or not re.search(r"1 passed, 0 failed", text):
            failed += 1
            print(f"FAILED (seed {seed}, program {p}): {path}\n{text[-800:]}")
        else:
            os.unlink(path)
    print(f"{programs} programs, {failed} failed ({skipped} too large or deep to compile)")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()

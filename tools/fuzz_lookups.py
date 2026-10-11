#!/usr/bin/env python3
"""Fuzz the lookup-shaped rewrites (SPEC §11.2) against a Python model.

Random programs read two input bundles and two numbers through the shapes the compiler turns
into tables and filters: runtime picks among bundle reads (`[a["coal"], a["stone"], …][i]`,
also next to an array indexed the same way), one-hot signal tables (`S1 if x == 1 else …`,
with and without 0 among the keys, keyed by a number or a bundle read), counts of matches
(`(a[s1] == k) + …`, scaled and subtracted), comparisons of bundle reads
(`a[s1] == b[s2] and …`) and running maxima. Each result goes to its own output.

usage: tools/fuzz_lookups.py [COUNT] [SEED]      (TICKY=./target/release/ticky)
"""
import os
import random
import subprocess
import sys
import tempfile

TICKY = os.environ.get("TICKY", "./target/release/ticky")
SIGNALS = ["iron-plate", "copper-plate", "coal", "stone", "signal-A", "signal-B", "signal-check"]
# Signals the one-hot tables pick (outputs as `{name=1}`).
PICKS = ["wood", "iron-ore", "copper-ore", "signal-X", "signal-Y", "water"]


def wrap(v):
    return (v + 2**31) % 2**32 - 2**31


def get(b, s):
    return b.get(s, 0)


class Gen:
    def __init__(self, r):
        self.r = r

    def index(self, n):
        """An index in 0..n-1 from x or y: (source, fn(env))."""
        v = self.r.choice(["x", "y"])
        off = self.r.randint(0, 3)
        return f"(({v} + {off}) % {n})", lambda env: (env[v] + off) % n

    def key(self):
        """A number to look up: x, y or a bundle read."""
        k = self.r.random()
        if k < 0.6:
            v = self.r.choice(["x", "y"])
            return v, lambda env: env[v]
        bn, s = self.r.choice(["a", "b"]), self.r.choice(SIGNALS)
        return f'{bn}["{s}"]', lambda env: get(env[bn], s)

    def pick(self, i):
        """`[a[s0], a[s1], …][ix]`, maybe beside an array indexed the same way."""
        n = self.r.randint(3, 5)
        bn = self.r.choice(["a", "b"])
        sigs = self.r.sample(SIGNALS, n)
        si, fi = self.index(n)
        lines = []
        src = f"[{', '.join(f'{bn}[{chr(34)}{s}{chr(34)}]' for s in sigs)}][{si}]"
        if self.r.random() < 0.5:
            vals = [self.r.randint(-5, 9) for _ in range(n)]
            lines.append(f"    arr{i} = [{', '.join(map(str, vals))}]")
            lines.append(f"    arr{i}[{si}] = x * 2")
            lines.append(f"    r{i} = {src} * 1000 + arr{i}[{si}]")

            def f(env):
                j = fi(env)
                v = list(vals)
                v[j] = wrap(env["x"] * 2)
                return wrap(get(env[bn], sigs[j]) * 1000 + v[j])
            return lines, f
        lines.append(f"    r{i} = {src}")
        return lines, lambda env: get(env[bn], sigs[fi(env)])

    def table(self, i):
        """A signal chosen by comparing a key with constants."""
        n = self.r.randint(3, 5)
        keys = self.r.sample(range(-2, 6) if self.r.random() < 0.5 else range(1, 9), n)
        sigs = self.r.sample(PICKS, n)
        ks, kf = self.key()
        arms = " else ".join(f'S("{s}") if {ks} == {c}' for s, c in zip(sigs, keys))
        lines = [f"    s{i} = {arms} else Bundle().argmax()"]

        def f(env):
            k = kf(env)
            for s, c in zip(sigs, keys):
                if k == c:
                    return s
            return None
        return lines, f

    def count(self, i):
        """`m * ((a[s1] == k) + …) - y`."""
        n = self.r.randint(3, 5)
        bn = self.r.choice(["a", "b"])
        sigs = self.r.sample(SIGNALS, n)
        k = self.r.choice([0, 1, 2, -3, 5])
        m = self.r.choice([1, -1, 3, 300, -300])
        terms = " + ".join(f'(1 if {bn}["{s}"] == {k} else 0)' for s in sigs)
        sub = self.r.random() < 0.5
        lines = [f"    r{i} = {m} * ({terms})" + (" - y" if sub else "")]
        return lines, lambda env: wrap(m * sum(1 for s in sigs if get(env[bn], s) == k) - (env["y"] if sub else 0))

    def compare(self, i):
        """A condition over reads of one bundle against numbers and the other bundle."""
        n = self.r.randint(2, 5)
        bn, other = self.r.sample(["a", "b"], 2)
        sigs = self.r.sample(SIGNALS, n)
        parts = []
        for s in sigs:
            op = self.r.choice(["==", "!=", "<", ">=", "<="])
            k = self.r.random()
            if k < 0.4:
                rhs, rf = f'{other}["{self.r.choice(SIGNALS)}"]', None
                t = rhs.split('"')[1]
                rf = lambda env, t=t: get(env[other], t)
            elif k < 0.7:
                v = self.r.choice(["x", "y"])
                rhs, rf = v, lambda env, v=v: env[v]
            else:
                c = self.r.randint(-3, 9)
                rhs, rf = str(c), lambda env, c=c: c
            parts.append((f'{bn}["{s}"] {op} {rhs}', s, op, rf))
        join = self.r.choice(["and", "or"])
        a, b = self.r.randint(-9, 9), self.r.randint(-9, 9)
        lines = [f"    r{i} = {a} if {f' {join} '.join(p[0] for p in parts)} else {b}"]
        ops = {"==": lambda p, q: p == q, "!=": lambda p, q: p != q, "<": lambda p, q: p < q,
               ">=": lambda p, q: p >= q, "<=": lambda p, q: p <= q}

        def f(env):
            res = [ops[op](get(env[bn], s), rf(env)) for _, s, op, rf in parts]
            ok = all(res) if join == "and" else any(res)
            return a if ok else b
        return lines, f

    def argmax(self, i):
        """A running maximum over bundle reads."""
        n = self.r.randint(3, 5)
        bn = self.r.choice(["a", "b"])
        sigs = self.r.sample(SIGNALS, n)
        ks = [self.r.randint(1, 9) for _ in range(n)]
        t0 = self.r.choice([0, 3])
        b0 = self.r.choice([0, -1])
        lines = [f"    best{i} = {b0}", f"    top{i} = {t0}"]
        for s, k in zip(sigs, ks):
            lines += [f'    if {bn}["{s}"] > top{i}:', f'        best{i}, top{i} = {k}, {bn}["{s}"]']
        lines.append(f"    r{i} = best{i}")

        def f(env):
            best, top = b0, t0
            for s, k in zip(sigs, ks):
                if get(env[bn], s) > top:
                    best, top = k, get(env[bn], s)
            return best
        return lines, f


def rand_bundle(r):
    return {s: r.randint(-4, 6) for s in r.sample(SIGNALS, r.randint(0, 6)) if r.random() < 0.9}


def main():
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 100
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    r = random.Random(seed)
    failed = 0
    for it in range(count):
        g = Gen(r)
        feats = [r.choice([g.pick, g.table, g.count, g.compare, g.argmax]) for _ in range(r.randint(1, 4))]
        shape = r.choice(["tick", "every", "main"])
        head = ["input a: Bundle", "input b: Bundle", "input x: int @ X", "input y: int @ Y"]
        body, checks = [], []
        outs = ["O", "P", "Q", "R"]
        for i, feat in enumerate(feats):
            lines, f = feat(i)
            body += lines
            if feat == g.table:
                head.append(f"output o{i}: Signal")
                body.append(f"    o{i} = s{i}")
            else:
                head.append(f"output o{i}: int @ {outs[i]}")
                body.append(f"    o{i} = r{i}")
            checks.append((f"o{i}", f, feat == g.table))
        if shape == "tick":
            src = head + ["every tick:"] + body
        elif shape == "every":
            src = head + ["every 30 ticks:"] + body
        else:
            src = head + ["while True:"] + body + ["    wait 3"]
        env = {"a": rand_bundle(r), "b": rand_bundle(r), "x": r.randint(-6, 9), "y": r.randint(-6, 9)}
        with tempfile.NamedTemporaryFile("w", suffix=".ticky", delete=False) as fh:
            fh.write("\n".join(src) + "\n")
            path = fh.name
        fmt = lambda b: ",".join(f"{s}:{v}" for s, v in b.items() if v != 0) or "{}"
        cmd = [TICKY, "sim", path, "--ticks", "300", f"--set=a={fmt(env['a'])}", f"--set=b={fmt(env['b'])}",
               f"--set=x={env['x']}", f"--set=y={env['y']}"]
        out = subprocess.run(cmd, capture_output=True, text=True, check=False)
        if out.returncode != 0:
            failed += 1
            print(f"[{it + 1}/{count}] COMPILE FAILURE {path}:\n{out.stderr[-800:]}")
            continue
        header = out.stdout.splitlines()[0].split()[1:]
        last = out.stdout.strip().splitlines()[-1].split()[1:]
        got = dict(zip(header, last))
        bad = {}
        for name, f, is_sig in checks:
            want = f(env)
            want = (f"{{{want}=1}}" if want else "{}") if is_sig else str(want)
            if got.get(name) != want:
                bad[name] = (want, got.get(name))
        if bad:
            failed += 1
            print(f"[{it + 1}/{count}] MISMATCH {path} ({shape}) env={env}: {bad}")
        if (it + 1) % 25 == 0:
            print(f"[{it + 1}/{count}] {failed} failures so far", flush=True)
    print(f"{count} programs, {failed} failures")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()

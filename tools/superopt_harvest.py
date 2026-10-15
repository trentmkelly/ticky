#!/usr/bin/env python3
"""Harvest superoptimisation targets (PLAN.md §4): the small scalar patterns codegen's
`logic()` emits (step and period blocks), with the combinators it spends on them.

Builds every program with `TICKY_SUPEROPT_HARVEST` (crates/ticky-compiler/src/fuse/superopt.rs
writes one line per pattern: cost, shape, leaf kinds, consumer, block) and aggregates by shape.

usage:
  tools/superopt_harvest.py [--ticky PATH] [--modes speed,size] [--top N] [--out FILE]
                            [--abstract] [--examples] [--corpus DIR]... [PROGRAM.ticky...]
  --abstract   group shapes that differ only in their constants (each class searched through
               its most frequent member)
  --out FILE   also write the aggregated table (tab-separated: count, total cost, shape, the
               most common leaf kinds) for `superopt search --targets FILE`
"""
import glob
import os
import re
import subprocess
import sys
import tempfile
from collections import Counter, defaultdict

# A constant operand in a shape (for --abstract: same shape up to constants).
CONST = re.compile(r"(?<=[ (])-?\d+(?=[ )])")

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)


def main():  # pylint: disable=too-many-locals,too-many-branches,too-many-statements
    args = sys.argv[1:]
    ticky = os.environ.get("TICKY", os.path.join(ROOT, "target", "release", "ticky"))
    modes = ["speed", "size"]
    top = 40
    out = None
    abstract = False
    progs = []
    while args:
        a = args.pop(0)
        if a == "--ticky":
            ticky = args.pop(0)
        elif a == "--modes":
            modes = args.pop(0).split(",")
        elif a == "--top":
            top = int(args.pop(0))
        elif a == "--abstract":
            abstract = True
        elif a == "--out":
            out = args.pop(0)
        elif a == "--examples":
            progs += sorted(glob.glob(os.path.join(ROOT, "examples", "*.ticky")))
        elif a == "--corpus":
            progs += sorted(glob.glob(os.path.join(args.pop(0), "**", "*.ticky"), recursive=True))
        else:
            progs.append(a)
    rows = []
    failed = 0
    with tempfile.TemporaryDirectory() as d:
        for p in progs:
            for m in modes:
                h = os.path.join(d, "h.tsv")
                if os.path.exists(h):
                    os.remove(h)
                env = dict(os.environ, TICKY_SUPEROPT_HARVEST=h)
                r = subprocess.run([ticky, "build", p, "--opt", m, "-o", os.devnull], env=env,
                                   capture_output=True, text=True, check=False)
                if r.returncode:
                    failed += 1
                    continue
                if os.path.exists(h):
                    # `--opt=size` compiles several candidate builds: keep the first (each
                    # logic() call writes a `#` header; a build ends when its first block's
                    # header comes round again).
                    first, calls = None, 0
                    with open(h, encoding="utf-8") as f:
                        for line in f:
                            if line.startswith("#\t"):
                                what = line.rstrip("\n").split("\t", 1)[1]
                                if calls and what == first:
                                    break
                                first = first if calls else what
                                calls += 1
                                continue
                            cost, shape, kinds, to, _what = line.rstrip("\n").split("\t", 4)
                            rows.append((m, int(cost), shape, kinds, to))
    for m in modes:
        sel = [r for r in rows if r[0] == m]
        by = defaultdict(list)
        for r in sel:
            by[CONST.sub("k", r[2]) if abstract else r[2]].append(r)
        total = sum(r[1] for r in sel)
        print(f"== {m}: {len(progs) - failed // max(1, len(modes))} programs, {len(sel)} patterns, "
              f"{len(by)} shapes, {total} combinators in them")
        ranked = sorted(by.items(), key=lambda kv: -sum(r[1] for r in kv[1]))
        print(f"{'count':>6} {'cost':>6} {'avg':>5}  shape   [leaf kinds; consumers]")
        for shape, rs in ranked[:top]:
            c = sum(r[1] for r in rs)
            kinds = Counter(r[3] for r in rs).most_common(2)
            tos = Counter(r[4] for r in rs).most_common(3)
            print(f"{len(rs):6d} {c:6d} {c / len(rs):5.2f}  {shape}   "
                  f"[{' '.join(f'{k or '-'}:{n}' for k, n in kinds)}; {' '.join(f'{k}:{n}' for k, n in tos)}]")
        if out:
            with open(out if len(modes) == 1 else f"{out}.{m}", "w", encoding="utf-8") as f:
                for shape, rs in ranked:
                    c = sum(r[1] for r in rs)
                    kinds = Counter(r[3] for r in rs).most_common(1)[0][0]
                    # With --abstract: the class's most frequent concrete shape stands for it.
                    rep = Counter(r[2] for r in rs).most_common(1)[0][0]
                    f.write(f"{len(rs)}\t{c}\t{rep}\t{kinds or '-'}\t{shape}\n")
    if failed:
        print(f"({failed} builds failed)")


if __name__ == "__main__":
    main()

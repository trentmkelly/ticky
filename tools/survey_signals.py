#!/usr/bin/env python3
"""Signal-pressure survey of compiled blueprints (written for PLAN.md §10, signal packing).

For each program: builds blueprint JSON, splits wires into networks, and reports
  - max distinct signals written onto any one network (actual per-wire pressure),
  - deciders already testing >= 2 distinct signals in one combinator (multi-flag tests),
  - deciders already holding/outputting >= 2 signals (flag sets held together),
  - bool producers (decider, constant output 1) and their readers: the extract cost packing
    would add (one AND/shift combinator per (bit, reader network) at least),
  - residual lane-mergeable groups: deciders with identical conditions and input networks but
    separate entities, and arithmetic combinators identical but for signal names (what packing
    or lane merging could fold at best).
Also: on the bus (the network with the most computed signals), how many signals are bools.
usage: tools/survey_signals.py [ticky build options] FILE...   (default: every example)
Uses TICKY if set, else target/release/ticky (build it first).
"""
import collections
import glob
import json
import os
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
T = os.environ.get("TICKY", os.path.join(ROOT, "target", "release", "ticky"))
COMB = {"decider-combinator", "arithmetic-combinator", "selector-combinator"}


def sig(s):
    if not s:
        return None
    return s.get("name") + ("@" + s["quality"] if s.get("quality") else "")


def survey(path, extra):
    with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as f:
        out = f.name
    r = subprocess.run([T, "build", path, "--json", "-o", out] + extra, capture_output=True, text=True, check=False, timeout=300)
    if r.returncode:
        return None
    with open(out, encoding="utf-8") as fh:
        bp = json.load(fh)["blueprint"]
    os.unlink(out)
    ents = {e["entity_number"]: e for e in bp["entities"]}
    parent = {}

    def find(x):
        parent.setdefault(x, x)
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x

    for a, ca, b, cb in bp["wires"]:
        parent[find((a, ca))] = find((b, cb))

    def nets(e, inp):
        n = e["entity_number"]
        if e["name"] in COMB:
            cs = (1, 2) if inp else (3, 4)
        else:
            cs = (1, 2)
        return tuple(find((n, c)) if (n, c) in parent else None for c in cs)

    written = collections.defaultdict(set)
    kinds = collections.defaultdict(set)
    readers = collections.defaultdict(set)  # (net, sig) -> entities reading it
    multi_test = multi_out = combs = 0
    bool_prod = []
    dec_groups = collections.defaultdict(list)
    ar_groups = collections.defaultdict(list)
    for e in ents.values():
        cb = e.get("control_behavior", {})
        name = e["name"]
        if name in COMB:
            combs += 1
        onets = [x for x in nets(e, False) if x is not None]
        inets = [x for x in nets(e, True) if x is not None] if name in COMB else []
        if name == "constant-combinator":
            for sec in cb.get("sections", {}).get("sections", []):
                for fl in sec.get("filters", []):
                    for n in onets:
                        written[n].add(sig(fl) if "name" in fl else None)
        elif name == "decider-combinator":
            d = cb.get("decider_conditions", {})
            conds = d.get("conditions", [])
            outs = d.get("outputs", [])
            tested = {sig(c.get("first_signal")) for c in conds} | {sig(c.get("second_signal")) for c in conds}
            tested.discard(None)
            if len(tested) >= 2:
                multi_test += 1
            if len(outs) >= 2:
                multi_out += 1
            for o in outs:
                for n in onets:
                    written[n].add(sig(o.get("signal")))
                isb = not o.get("copy_count_from_input", True) and o.get("constant", 1) == 1
                for n in onets:
                    kinds[(n, sig(o.get("signal")))].add("b" if isb else "o")
                if isb:
                    bool_prod.append((tuple(onets), sig(o.get("signal"))))
            for s in tested:
                for n in inets:
                    readers[(n, s)].add(e["entity_number"])
            key = (json.dumps(conds, sort_keys=True), tuple(sorted(inets)), tuple(sorted(onets)))
            dec_groups[key].append(e["entity_number"])
        elif name == "arithmetic-combinator":
            a = cb.get("arithmetic_conditions", {})
            for n in onets:
                written[n].add(sig(a.get("output_signal")))
                kinds[(n, sig(a.get("output_signal")))].add("o")
            for k in ("first_signal", "second_signal"):
                s = sig(a.get(k))
                if s:
                    for n in inets:
                        readers[(n, s)].add(e["entity_number"])
            shape = (a.get("operation"), a.get("second_constant"), a.get("first_constant"), bool(a.get("second_signal")),
                     tuple(sorted(inets)), tuple(sorted(onets)))
            if "each" not in str(a.get("first_signal")):
                ar_groups[shape].append(e["entity_number"])
        elif name == "selector-combinator":
            for n in onets:
                written[n].add("selector:" + str(e["entity_number"]))
    maxsig = max((len(v) for v in written.values()), default=0)
    # The network with the most signals written by deciders/arithmetic (the bus): bool-only signals on it.
    cnt = collections.Counter(n for (n, _s) in kinds)
    busn = cnt.most_common(1)[0][0] if cnt else None
    bus_sigs = cnt[busn] if busn else 0
    bus_bool = sum(1 for (n, _s), k in kinds.items() if n == busn and k == {"b"})
    # Bool producers and the readers an extract would serve.
    extract = 0
    for onets, s in bool_prod:
        rs = set()
        for n in onets:
            rs |= readers.get((n, s), set())
        extract += max(1, len(rs))
    dec_merge = sum(len(v) - 1 for v in dec_groups.values() if len(v) > 1)
    ar_merge = sum(len(v) - 1 for v in ar_groups.values() if len(v) > 1)
    return dict(bus_sigs=bus_sigs, bus_bool=bus_bool, combs=combs, maxsig=maxsig, nets=len(written), multi_test=multi_test, multi_out=multi_out,
                bools=len(bool_prod), extract=extract, dec_merge=dec_merge, ar_merge=ar_merge)


def main():
    extra = [a for a in sys.argv[1:] if a.startswith("--")]
    files = [a for a in sys.argv[1:] if not a.startswith("--")]
    if not files:
        files = sorted(glob.glob(os.path.join(ROOT, "examples", "*.ticky")))
    tot = collections.Counter()
    print(f"{'program':28} {'combs':>5} {'maxsig':>6} {'multitest':>9} {'multiout':>8} {'bools':>5} {'extract':>7} {'decmerge':>8} {'armerge':>7} bus")
    for p in files:
        try:
            s = survey(p, extra)
        except subprocess.TimeoutExpired:
            s = None
        if s is None:
            print(f"{os.path.basename(p):28} FAIL")
            continue
        tot.update({k: v for k, v in s.items() if k != "maxsig"})
        tot["maxsig_max"] = max(tot["maxsig_max"], s["maxsig"])
        print(f"{os.path.basename(p):28} {s['combs']:>5} {s['maxsig']:>6} {s['multi_test']:>9} {s['multi_out']:>8} {s['bools']:>5} {s['extract']:>7} {s['dec_merge']:>8} {s['ar_merge']:>7} {s['bus_bool']}/{s['bus_sigs']} bool", flush=True)
    print("TOTAL", dict(tot))


if __name__ == "__main__":
    main()

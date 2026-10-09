#!/usr/bin/env python3
"""Fuzz Ticky's runtime signals (SPEC §4.3.4) against a Python model.

Random bundles (with ties and negative values) go through loops over `.items()` (either
order, with `break`/`continue`), signal comparisons, runtime-key writes, `argmax`, `argmin`
and `nth` with a runtime rank. Python sorts like the game's selector: by value, ties in the
game's signal order (items, fluids, virtual signals, each in prototype order).

usage: tools/fuzz_signals.py [COUNT] [SEED]
"""
import os
import random
import subprocess
import sys
import tempfile

TICKY = os.environ.get("TICKY", "./target/debug/ticky")
# In the game's tie order.
SIGNALS = ["wood", "coal", "stone", "iron-ore", "iron-plate", "copper-plate", "water", "crude-oil",
           "signal-0", "signal-A", "signal-B"]
RANK = {s: i for i, s in enumerate(SIGNALS)}


def ordered(b, ascending):
    """The signals of bundle `b` in loop order."""
    items = [(s, v) for s, v in b.items() if v != 0]
    if ascending:
        return sorted(items, key=lambda x: (x[1], -RANK[x[0]]))
    return sorted(items, key=lambda x: (-x[1], RANK[x[0]]))


def gen(r):
    """A random program body (as lines) and a Python function computing its outputs."""
    asc = r.random() < 0.4
    mod = r.choice([7, 13, 1000])
    special = r.choice(SIGNALS)
    bonus = r.randint(1, 9)
    stop = r.choice([None, "break", "continue"])
    limit = r.randint(-3, 6)
    lines = [
        "    h = 0",
        "    n = 0",
        "    c = Bundle()",
        f"    for s, v in b.items(ascending={asc}):",
        f"        h = (h * 3 + v) % {mod}",
        f"        if s == S(\"{special}\"):",
        f"            h += {bonus}",
        "        c[s] = h + 1",
    ]
    if stop:
        lines += [f"        if v > {limit}:", f"            {stop}"]
    lines += ["        n += 1"]

    def model(b, k):
        h, n, c = 0, 0, {}
        for s, v in ordered(b, asc):
            h = (h * 3 + v) % mod
            if s == special:
                h += bonus
            c[s] = h + 1
            if stop and v > limit:
                if stop == "break":
                    break
                continue
            n += 1
        srt = ordered(b, False)
        top = srt[0][0] if srt else None
        low = ordered(b, True)[0][0] if srt else None
        kth = srt[k] if 0 <= k < len(srt) else (None, 0)
        return {"h": h, "n": n, "c": {s: v for s, v in c.items() if v != 0}, "top": top, "low": low, "kth": kth[0], "kv": kth[1]}
    return lines, model


def main():  # pylint: disable=too-many-locals
    """Runs the fuzzer."""
    count = int(sys.argv[1]) if len(sys.argv) > 1 else 50
    seed = int(sys.argv[2]) if len(sys.argv) > 2 else 1
    r = random.Random(seed)
    failed = 0
    for _ in range(count):
        lines, model = gen(r)
        sigs = r.sample(SIGNALS, r.randint(0, 6))
        b = {s: r.choice([r.randint(-5, 9), 3]) for s in sigs}
        b = {s: v for s, v in b.items() if v != 0}
        k = r.randint(-1, 5)
        want = model(b, k)
        src = "\n".join([
            "input b: Bundle", "input k: int @ K", "input go: bool @ G",
            "output oh: int @ H", "output on: int @ N", "output oc: Bundle", "output top: Signal",
            "output low: Signal", "output kth: Signal", "output kv: int @ V", "output done: bool @ D",
            "while True:", "    wait until go",
        ] + lines + [
            "    oh = h", "    on = n", "    oc = c", "    top = b.argmax()", "    low = b.argmin()",
            "    kth, kv = b.nth(k)", "    done = True", "    wait until not go",
        ]) + "\n"
        with tempfile.NamedTemporaryFile("w", suffix=".ticky", delete=False) as f:
            f.write(src)
            path = f.name
        bundle = ",".join(f"{s}:{v}" for s, v in b.items()) or "{}"
        cmd = [TICKY, "sim", path, "--ticks", "400", f"--set=b={bundle}", f"--set=k={k}", "--set=go=1@3"]
        out = subprocess.run(cmd, capture_output=True, text=True, check=False)
        if out.returncode != 0:
            failed += 1
            print(f"COMPILE FAILURE ({path}):\n{out.stderr}")
            continue
        header = out.stdout.splitlines()[0].split()[1:]
        last = out.stdout.strip().splitlines()[-1].split()[1:]
        got = dict(zip(header, last))
        one = lambda x: f"{{{x}=1}}" if x else "{}"
        cstr = "{" + ",".join(f"{s}={v}" for s, v in sorted(want["c"].items(), key=lambda x: SIGNALS.index(x[0]))) + "}"
        expect = {"oh": str(want["h"]), "on": str(want["n"]), "top": one(want["top"]), "low": one(want["low"]),
                  "kth": one(want["kth"]), "kv": str(want["kv"]), "done": "1"}
        bad = {key: (expect[key], got.get(key)) for key in expect if expect[key] != got.get(key)}
        gotc = dict(x.split("=") for x in got.get("oc", "{}").strip("{}").split(",") if x)
        if {s: int(v) for s, v in gotc.items()} != want["c"]:
            bad["oc"] = (cstr, got.get("oc"))
        if bad:
            failed += 1
            print(f"MISMATCH ({path}) b={b} k={k}: {bad}")
    print(f"{count} programs, {failed} failures")
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()

#!/usr/bin/env bash
# Compile every example and report combinators, steps, latency and footprint.
# Builds a fresh release compiler unless TICKY names an existing binary.
# Usage (from anywhere): tools/bench.sh [--opt=size] [other `ticky check` options]
# Save stdout before/after a change and diff the tables; diagnostics go to stderr.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
if [[ -z ${TICKY:-} ]]; then
  cargo build --quiet --release --locked --package ticky-cli \
    --manifest-path "$ROOT/Cargo.toml" --target-dir "$ROOT/target"
  TICKY="$ROOT/target/release/ticky"
fi

python3 -u - "$ROOT" "$TICKY" "$@" <<'PY'
import re
import subprocess
import sys
from pathlib import Path

root, compiler, *options = sys.argv[1:]
files = sorted((Path(root) / "examples").glob("*.ticky"))
if not files:
    sys.exit("bench: no examples found")

print(f"{'example':<24} {'combs':>6} {'steps':>6} {'latency':>10} {'tiles':>10}")
total_combs = total_steps = total_tiles = 0
failed = []
for path in files:
    try:
        result = subprocess.run(
            [compiler, "check", str(path), *options],
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True,
        )
    except OSError as error:
        sys.exit(f"bench: cannot run {compiler}: {error}")
    report = result.stdout
    count = re.search(r"total: (\d+) combinators", report)
    footprint = re.search(r"(\d+)×(\d+) tiles", report)
    if result.returncode or not count or not footprint:
        failed.append(path.name)
        print(f"{path.name:<24} error")
        print(f"bench: {path.name} failed (exit {result.returncode})\n{report}", file=sys.stderr)
        continue
    combs = int(count[1])
    steps = re.search(r"main program +(\d+) steps", report)
    latency = ",".join(re.findall(r"latency (\d+)", report)) or "-"
    width, height = map(int, footprint.groups())
    print(f"{path.name:<24} {combs:>6} {steps[1] if steps else '-':>6} {latency:>10} {f'{width}x{height}':>10}")
    total_combs += combs
    total_steps += int(steps[1]) if steps else 0
    total_tiles += width * height

label = f"SUBTOTAL ({len(files) - len(failed)}/{len(files)})" if failed else "TOTAL"
print(f"{label:<24} {total_combs:>6} {total_steps:>6} {'-':>10} {total_tiles:>10}")
if failed:
    sys.exit(f"bench: {len(failed)}/{len(files)} examples failed; subtotal excludes failures")
print(f"bench: compiled all {len(files)} examples; combinator counts exclude constants", file=sys.stderr)
PY

#!/usr/bin/env bash
# Cost of every example: combinators, main-program steps, every-tick latencies, footprint.
# usage: tools/bench.sh > before.txt; (change things); tools/bench.sh > after.txt; diff before.txt after.txt
T=${TICKY:-./target/release/ticky}
printf "%-14s %6s %6s %10s %8s\n" example combs steps latency tiles
for f in examples/*.ticky; do
  n=$(basename "$f" .ticky)
  $T check "$f" 2>&1 | python3 -c "
import sys, re
t = sys.stdin.read()
c = re.search(r'total: (\d+) combinators', t)
if not c:
    print(f'{\"$n\":<14} {\"error\":>6}'); sys.exit()
m = re.search(r'main program +(\d+) steps', t)
l = ','.join(re.findall(r'latency (\d+)', t)) or '-'
w = re.search(r'(\d+)×(\d+) tiles', t)
print(f'{\"$n\":<14} {c.group(1):>6} {m.group(1) if m else \"-\":>6} {l:>10} {w.group(1)+\"x\"+w.group(2):>8}')"
done

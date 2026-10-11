#!/usr/bin/env bash
# In-game difftest of examples/cubium-generator.ticky with the Cubium mod loaded (Space Age).
# usage: T=<ticky binary> CUBIUM=<path to the unpacked cubium mod> harness/difftest-cubium.sh
T=${T:-./target/debug/ticky}
CUBIUM=${CUBIUM:-$(cd "$(dirname "$0")/../.." && pwd)/cubium}
printf "%-26s " cubium-generator.ticky
TICKY_SPACE_AGE=1 TICKY_EXTRA_MODS="cubium=$CUBIUM" timeout 400 $T difftest examples/cubium-generator.ticky --space-age --ticks 1600 \
 --set 'warehouse=energized-microcube:10,dormant-microcube:10,copper-plate:100@2' \
 --set 'crafter_status=signal-A:4,signal-C:2@300' \
 --set 'warehouse=energized-microcube:10,cube-jelly:40,copper-plate:100@350' \
 --set 'warehouse=energized-microcube:20,cube-jelly:300,copper-plate:5000,iron-plate:100@500' \
 --set 'crafter_status={}@700' \
 --set 'warehouse=energized-microcube:1,dormant-microcube:1499,cube-jelly:1498@800' \
 --set 'crafter_status=signal-B:1,signal-D:3@1000' \
 --set 'warehouse=energized-microcube:100,cube-jelly:1200,copper-plate:100@1100' \
 --set 'warehouse={}@1400' 2>&1 | grep -E "MATCH|tick [0-9]|error|game trace" | head -4

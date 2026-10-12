#!/usr/bin/env bash
# In-game difftest of examples/holmium-generator.ticky with the Cubium mod loaded (Space Age).
# usage: T=<ticky binary> CUBIUM=<path to the unpacked cubium mod> harness/difftest-holmium.sh
T=${T:-./target/debug/ticky}
CUBIUM=${CUBIUM:-$(cd "$(dirname "$0")/../.." && pwd)/cubium}
printf "%-26s " holmium-generator.ticky
TICKY_SPACE_AGE=1 TICKY_EXTRA_MODS="cubium=$CUBIUM" timeout 400 $T difftest examples/holmium-generator.ticky --space-age --ticks 1500 \
 --set 'warehouse=energized-microcube:50,water:10000,light-oil:10000@2' \
 --set 'warehouse=energized-microcube:50,cube-jelly:30@130' \
 --set 'warehouse=steel-plate:400,energized-microcube:100,inverted-microcube:20,cube-jelly:300,dream-concentrate:5000,liquid-hope:5000@260' \
 --set 'belt=steel-plate:30,cube-jelly:120@260' \
 --set 'belt={}@390' \
 --set 'warehouse=energized-microcube:50,dormant-microcube:500,cube-jelly:300,dream:6000,spoilage:30@390' \
 --set 'warehouse=inverted-dormant-microcube:5,inverted-microcube:20,liquid-fear:5000,liquid-courage:500,liquid-dream:5000,liquid-anger:500,emotional-tar:500,water:10000,light-oil:1000,dream-concentrate:3000,dream:100,liquid-hate:2000,liquid-disgust:1000,energized-microcube:100@520' \
 --set 'warehouse=liquid-hope:15000,liquid-disgust:15000,dormant-microcube:20,energized-microcube:100,liquid-dream:1000,solid-fuel:40,steam:600@650' \
 --set 'warehouse=liquid-hate:20000,liquid-anger:17000,liquid-disgust:800,energized-microcube:5,emotional-tar:500,water:1000@780' \
 --set 'warehouse=energized-microcube:100,cube-jelly:450,dream:700@910' \
 --set 'rotting=destabilized-cube-matter:300@910' \
 --set 'warehouse=copper-ore:100,iron-ore:100,iron-plate:50@1040' \
 --set 'rotting={}@1170' \
 --set 'warehouse={}@1300' 2>&1 | grep -E "MATCH|tick [0-9]|error|game trace" | head -4

#!/usr/bin/env bash
# Runs every example through `ticky difftest` with representative inputs.
T=${T:-./target/debug/ticky}
run(){ printf "%-26s " "$(basename $1)"; timeout 280 $T difftest "$@" 2>&1 | grep -E "MATCH|tick [0-9]|error|game trace" | head -4; }
run examples/blinker.ticky --ticks 200
run examples/hysteresis.ticky --ticks 200 --set charge=10@5 --set charge=50@40 --set charge=90@80 --set charge=15@130 --set charge=85@131 --set charge=10@132
run examples/math.ticky --ticks 400 --set x=-7 --set y=2 --set y=-2@50 --set x=7@100 --set y=0@150 --set x=-2147483648@200 --set y=-1@250 --set x=123456@300 --set y=-37@330 --set x=5@360
run examples/counters.ticky --ticks 300 --set step=3 --set step=-7@100 --set RUN=0@200 --set RUN=1@210
run examples/thermostat.ticky --ticks 400 --set temp=20 --set temp=90@150 --set temp=-50@300
run examples/demo.ticky --ticks 400 --set a=-7 --set a=150@100 --set a=70@200 --set a=10@300 --set RUN=0@330 --set RUN=1@340
run examples/fib.ticky --ticks 400 --set n=20 --set start=1@3 --set start=0@10 --set n=46@150 --set start=1@160 --set start=0@170 --set n=-3@300 --set start=1@310
run examples/collatz.ticky --ticks 1500 --set x=27@2 --set x=97@700 --set x=-5@1300 --set x=1@1400
run examples/primes.ticky --ticks 1500 --set limit=60
run examples/button.ticky --ticks 200 --set button=1@10 --set button=0@20 --set button=3@21 --set button=0@40 --set button=1@41 --set button=0@42 --set RUN=0@100 --set RUN=1@110 --set button=1@150
run examples/guess.ticky --ticks 400 --set guess=50 --set submit=1@30 --set submit=0@40 --set guess=25@60 --set submit=1@70 --set submit=0@80 --set guess=75@100 --set submit=1@110 --set submit=0@120
run examples/tally.ticky --ticks 300 --set items=3 --set items=0@40 --set reset=1@60 --set reset=0@61 --set items=-2@70 --set items=5@100 --set reset=1@150 --set items=7@160 --set reset=0@170 --set RUN=0@220 --set RUN=1@230
run examples/calculator.ticky --ticks 2000 --set n=27 --set start=1@5 --set start=0@900 --set n=10@910 --set start=1@920 --set start=0@1100 --set n=0@1110 --set start=1@1120 --set start=0@1300 --set n=-5@1310 --set start=1@1320 --set RUN=0@1500 --set RUN=1@1510
run examples/functions.ticky --ticks 400 --set a=84 --set b=-36 --set a=5@120 --set b=7@121 --set a=150@250 --set b=0@300 --set RUN=0@350 --set RUN=1@360
run examples/arrays.ticky --ticks 500 --set pick=3 --set value=10 --set store=1@5 --set store=0@40 --set pick=9@80 --set pick=5@120 --set value=-7@120 --set store=1@125 --set store=0@160 --set pick=-1@200 --set pick=5@240
run examples/stats.ticky --ticks 1500 --set reading=100 --set reading=180@250 --set reading=-40@700 --set reading=55@1000 --set RUN=0@1300 --set RUN=1@1310
run examples/requester.ticky --ticks 60 --set 'stock=iron-plate:150,copper-plate:500,plastic-bar:200,coal:1000@5' --set 'stock=iron-plate:400,steel-plate:30@30'
run examples/inventory.ticky --ticks 80 --set limit=100 --set 'stock=iron-plate:40,copper-plate:250,coal:-5,stone:100@3' --set 'stock=copper-plate:5,stone:1000@40' --set limit=7@60
run examples/deliveries.ticky --ticks 120 --set 'stock=iron-plate:100,coal:50@2' --set mark=1@20 --set mark=0@30 --set 'stock=iron-plate:130,coal:20,stone:5,wood:1,copper-ore:3@50' --set 'stock=iron-plate:100@90'
run examples/bundles.ticky --ticks 200 --set 'stock=iron-plate:5,copper-plate:2@1' --set reset=1@45 --set reset=0@70 --set mode=1@80 --set mode=0@100 --set mode=2@110 --set 'stock=copper-plate:1,coal:3@130' --set mode=0@150 --set mode=3@160
run examples/sorting.ticky --ticks 3200 --set seed=7 --set go=1@5 --set go=0@1500 --set seed=3@1510 --set go=1@1520 --set seed=-13@2900
run examples/histogram.ticky --ticks 400 --set ask=5 --set sample=5@10 --set strobe=1@12 --set strobe=0@22 --set sample=9@30 --set strobe=1@32 --set strobe=0@42 --set sample=5@50 --set strobe=1@52 --set strobe=0@62 --set sample=63@70 --set strobe=1@72 --set strobe=0@82 --set sample=70@90 --set strobe=1@92 --set strobe=0@102 --set ask=63@150 --set sample=-4@200 --set strobe=1@202 --set strobe=0@260 --set ask=-1@300
run examples/handshake.ticky --ticks 900 --set ore=5000 --set ore=10@50 --set ore=5000@420 --set ore=500@500 --set RUN=0@800 --set RUN=1@810
run examples/checks.ticky --checks --ticks 300 --set a=10 --set b=2@5 --set i=1@5 --set b=0@30 --set a=0@40 --set a=5@60 --set i=7@70 --set b=1@80 --set b=0@120 --set RUN=0@150 --set RUN=1@160 --set a=3@160 --set i=2@160 --set b=1@170 --set a=900@200 --set b=0@210 --set b=1@220
run examples/signals.ticky --ticks 200 --set want=coal --set k=2 --set 'stock=iron-plate:30,copper-plate:50,coal:10,stone:50' --set k=7@30 --set want=wood@40 --set 'stock=iron-plate:30,copper-plate:5@60' --set 'stock=wood:3,coal:3,signal-A:3@110' --set k=1@120 --set want=signal-A@130 --set 'stock={}@160'
run examples/dispatch.ticky --ticks 100 --set 'demand=signal-A:3,signal-B:9,signal-C:5' --set train_waiting=1@5 --set train_waiting=0@20 --set 'demand=signal-C:30,signal-B:30@25' --set train_waiting=1@30 --set train_waiting=0@50 --set 'demand={}@55' --set train_waiting=1@60
run examples/ranking.ticky --ticks 200 --set 'stock=iron-plate:3,copper-plate:5,coal:1' --set pick=iron-plate --set go=1@2 --set go=0@60 --set 'stock=wood:4,coal:4,signal-A:4,water:-2@70' --set pick=coal@70 --set go=1@80

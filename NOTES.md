# Ticky — implementation notes and progress

Newest entries at the bottom. Read SPEC.md for the language; this file is about how the
compiler actually works and what has been verified.

## 2026-10-08 — Level 0 done

**Scope:** ports (`int`/`bool`), constants, state with initial values, `every tick:` /
`every N ticks:` blocks with assignments, tuple assignment, `if/elif/else`, all scalar operators
with Python semantics, builtins `abs min max clamp tdiv tmod int bool`, `test` blocks, simulator,
blueprint output with a naive grid layout, RUN switch.

### Codegen scheme (codegen.rs)

- **One green bus.** Every value gets its own signal (no reuse yet), and every core combinator's
  input and output sit on one shared green network. Simple and always correct; signal
  colouring/reuse comes later. 358 base-game signals are available, so ~300 values max.
- **Multi-cycle blocks.** A block with logic depth D runs with period N ≥ D+1. A clock decider,
  fed +1 by the RUN switch, cycles phases 1..N. Two pulses per period:
  - **EI** (phase 1) loads sample registers for inputs and other blocks' state, so sources hold
    still during the iteration;
  - **ES** (phase `(1+D) % N + 1`) commits next-state values into the block's registers.
  When ES and EI share a phase (N = D+1), a **WARM** latch set by the first EI suppresses the
  first ES, which would otherwise commit garbage.
- **Registers:** a hold decider `[ES == 0 ∧ ST == 0 ∧ RUN ≠ 0] → X (copy)`, a load arithmetic
  `next * ES → X`, and an init decider `[ST ≠ 0] → X = init` when init ≠ 0.
- **Start:** RP = RUN delayed one tick; ST = RUN ∧ ¬RP, a one-tick pulse on the rising edge that
  loads initial values. The clocks and pulses are gated on RP, so the first EI comes right after
  ST. RUN off clears everything; outputs are `X * RUN`, so they read 0.
- **Mux:** `(a * t) + (b * f)` as two arithmetic combinators writing the same signal (summed on
  the wire), where t and f are complementary 0/1 conditions computed in parallel.
- **Python `//` and `%`:** truncating op plus a sign correction (+2 depth), skipped when interval
  analysis proves both operands non-negative. Block state intervals come from a fixpoint over the
  block (with widening), so e.g. `(x + 1) % 600` is known to stay in 0..599.

### Verified against the real game (Factorio 2.0.77)

- Integer edge cases (ops.rs tests): `/` and `%` by 0 → 0, `MIN / -1` → 0, shift amounts masked
  to 5 bits, arithmetic `>>`, wrapping `^`, negative exponents → truncated reciprocal.
- Decider conditions group as OR-of-ANDs.
- `ticky difftest` on every example matches the simulator tick for tick (blinker, hysteresis, math
  with MIN/-1/0 divisors, two-block counters incl. RUN off/on/1-tick pulse, thermostat, demo).
- **Harness timing offset:** the Lua harness observes outputs exactly 1 tick later than the
  simulator records them, uniformly. difftest compares `game[i+1]` with `sim[i]`.

### Harness (harness/)

`run.sh JOB.lua` runs the `ticky-harness` scenario on a headless server (≈2 s, sandbox in
`/tmp/ticky-harness`). Set `TICKY_SCREENSHOT=1` (and `screenshot = true` in the job) for a
windowed run that saves `shot.png`. The server quits on stdin EOF, so the script holds a FIFO open.

### Known limitations at that point (see the next entry for what changed)

- Period is D+1 even for feed-forward logic. The spec's targets (P = 1 for common patterns,
  fused multi-condition deciders, `x = (x + 1) % N` in one decider) need pipelining/retiming and
  peephole fusion: build-order step 8.
- No signal reuse; no error lamp yet (SPEC §13 arrives with `--checks`).
- Layout is a plain grid with an MST of wires; fine up to a few hundred combinators.

## 2026-10-08 (later) — Level 1 and the speed work

### Level 1: sequential code (cfg.rs, program.rs, codegen.rs `main_proc`)

- **Prologue.** Leading top-level constant assignments (each name once) are constants or
  initial values; everything after them is the `main` process. Keeps level 0 programs meaning
  the same thing.
- **CFG of steps** (cfg.rs): straight-line code with simple `if`s if-converted in place;
  `while`/`for`/`wait`/`break`/`continue` create steps. Loops are rotated (test at the end of
  the previous step and of the body). `for` uses hidden variables `i#kN` (counter) and
  `i#endN` (end, when not constant); the loop variable is a copy of the counter so it keeps its
  last value like Python. Empty jump steps are threaded away after constant folding.
- **State machine:** PC register (step id, 0 = halted), step timer T (counter trick: decider
  loop through a +1 constant on a private red wire), and per step a commit decider
  `[PC == s ∧ ANY == 0 ∧ T == settle (∧ wait condition)] → CM_s, ANY`. ANY (also emitted by ST)
  resets T, reloads input samples and lets the PC reload. Step duration = max(depth, 1) + 1.
- Inputs, other processes' state and `ticks()` are sampled on ANY; `wait until` reads live
  (unsampled) versions. Definite-assignment analysis over steps rejects reads of unassigned
  variables. Dead variables (never read, not outputs) get no register.

### Speed work

- **Fusion** (fuse.rs): boolean expressions (comparisons with and/or/not/xor, selects between
  constants or booleans) become DNF deciders (`Op::Dec`, ≤ 12 terms / 32 literals); branch,
  wait and commit deciders inline their conditions.
- **Guarded loads**: a register's next value is split along its select tree into loads under
  conditions; paths that keep the old value just hold. Constant loads are *direct* (the load
  decider checks the condition on the commit tick, and the hold decider gets the negated
  condition as "keep"); value loads get an enable decider one tick earlier.
- **Peepholes**: `// 2^k` → `>>`, `% 2^k` → `&`, `a % b == 0` uses the truncating remainder,
  `x ± k <op> c` → `x <op> c ∓ k` when intervals rule out wrapping.
- **Pipelining** (pipeline.rs): `every tick:` blocks whose states don't feed back through
  logic run every tick; τ offsets per node, delay chains for alignment, input latency L, and a
  start-up delay line (`warm` taps) so the first commit happens after the pipeline has filled.
  **Accumulators** `x += w` (conditional, with constant overrides like reset) use the counter
  trick on a private red loop, plus an "idle" hold that doesn't add before the block starts.
- **Signal namespaces** (codegen `logic`): logic is cut into clusters of 250 combinators; values
  used only inside their cluster live on the cluster's red wire with their own signal pool, and
  every operand names its wire. Lifts the 358-value ceiling (a 582-combinator fuzz program now
  compiles and matches the game).
- `--opt=size` compiles with and without pipelining and keeps the smaller.

Before → after on the examples: hysteresis period 4 → 1 (19 → 7 combinators); demo `every
tick` 4 → 1; thermostat 14 → 6; Fibonacci loop 3 → 2 ticks/iteration; Collatz 7 → 4; primes
below 100: 3187 → 1509 ticks; button counter 22 → 16 combinators.

### Verification

- `harness/difftest-examples.sh`: every example, in the real game vs. the simulator (all match).
- Fuzzers against **Python itself** (tools/): `fuzz_exprs.py` (random expressions, `every tick`
  outputs), `fuzz_programs.py` (random sequential programs with loops/break/continue, final
  values), `fuzz_blocks.py` (random stateful `every tick` blocks; Python replays exactly as
  many iterations as the block reports). Thousands of cases, all matching, after fixing what
  they found (constant-folded selects/loads after fusion).
- Found along the way: a `wait until` condition computed through combinators could be read one
  tick early (fixed: waits check `T ≥ ready`); pipelined blocks could commit stale pipeline
  contents at start (fixed: warm-up).

### Ideas not done yet

- One-tick steps (chain zero-depth steps), loop pipelining in `main`.
- `x = (x + k) % N` as one decider + constant (the classic clock) for P = 1 counters.
- Hoisting input-only subexpressions out of multi-cycle blocks (shorter period).
- Proper placement (wire lengths, compactness) instead of the serpentine grid.

## 2026-10-08 (evening) — Level 2: functions and arrays

### Expansion pass (expand.rs), before analysis

- **Shapes.** Every variable is a scalar or an array of fixed length (first assignment wins;
  conflicts are errors). Two rounds: the first discovers module-level shapes (they may be used
  before being assigned in file order), the second expands.
- **Arrays → scalars.** `xs` of length N becomes `xs[0]`…`xs[N-1]`. Constant indexes name the
  element; runtime reads become `#select(i, x0, …)` (IR `Op::Sel`: Σ (i==k)·xk, one gate per
  element on a shared signal, interval analysis drops impossible arms); runtime writes become one
  `if i == k: xs[k] = v` per element (→ guarded loads). Builtins `len/sum/min/max/any/all`
  reduce as balanced trees; `in`; comprehensions over constant ranges or arrays.
- **Functions.** Calls are hoisted out of expressions in evaluation order; calls inside
  `and`/`or`/`if-else` become real `if`s (keeps Python's short-circuiting). Straight-line
  functions are **inlined** into a `Block{label}` (locals `f.<id>.<name>`, `return` →
  assign `#ret` slots + `Exit(label)`). Functions with loops/waits (or calling such), when called
  from sequential code, are **subroutines**: body expanded once (locals `f.<name>`), params
  assigned at the call site, `Call(f)`, results copied to temporaries right after.
- **Every blocks**: all calls inline, `for` loops unroll into labelled blocks (`break`/
  `continue` → `Exit`), then `flatten` removes Block/Exit by moving the code after an `if` into
  the branches that reach it (bounded by a budget).
- **cfg.rs**: flattenable blocks are flattened in place (stay inside a step); others get a
  continuation step; `Exit` → goto; `Call` → `Term::Call` (+ continuation); subroutine bodies
  are built after main with `Term::Return`. Codegen: a return-address register per subroutine,
  PC ← constant on call, PC ← `ret * CM` on return.
- **Definite assignment** is call-site sensitive: a call flows into the subroutine and,
  separately, to its own continuation with whatever the subroutine always assigns.
- **Compile-time prologue** (consteval.rs): leading top-level statements that only use
  constants are *executed* by an interpreter (loops, ifs, inlined and subroutine calls); their
  results become constants / initial values.

### Fixes found on the way
- Guarded-load splitting followed every path of deep select trees (unrolled sorts) and
  multiplied loads combinatorially; now only the top level always splits, deeper only where a
  path keeps the old value or loads a constant, at most 8 loads.
- Inline-everything blew up on functions with loops called from many places (compile time and
  "out of signals"); subroutines fixed both.

### Status
- All 16 examples difftest-match the game (including `functions`, `arrays`, `stats`).
- `tools/fuzz_level2.py` (functions + arrays vs Python): one 60-program run had 55 passing;
  the visible failures were capacity limits ("out of signals" on a huge nested-call program,
  "too much branching" from a long short-circuit chain), not wrong answers. A complete,
  size-capped run is still to do (the output of that run was truncated).

## 2026-10-08 (night) — Level 3: bundles

### Verified first (harness/ticky-harness/scenarios/probe)
A probe scenario builds combinators directly and records their outputs; the simulator test
`wildcard_tests::matches_the_game` reproduces every result. Findings the design relies on:
`each(red) op signal(green)`; `each(red) op each(green)` over the union of signals (so `a + b`
is one combinator); `each` in several decider conditions plus ordinary ones; a single output
of an `each` decider sums (constant 1 → count); `everything` copy; selector `select`/`count`
(blueprint: `{"operation": "select", "select_max": true, "index_constant": 0}`).

### Signals (ticky-factorio/src/signals.rs)
- One global table: base game (internal wiring only uses these), then
  `data/signals-extra.tsv` (recipes + Space Age/Quality/Elevated Rails, dumped with
  `TICKY_SPACE_AGE=1 TICKY_SCENARIO=dump harness/run.sh`), then names programs make up:
  `intern(kind, name)` adds them (`known = false`) and the compiler warns.
- `SignalKind` covers recipe, quality, space-location, asteroid-chunk.

### Compiler
- **IR** (ir.rs): bundle nodes `BConst`, `Bun(terms)` (a bundle is the sum of its terms, each
  one combinator writing the bundle's wire: `Map` = each op k, `RMap` = k op each, `Zip` =
  each(red) op each(green), `One` = scalar → one signal, `Filter`, `DFilter`, `K` = constant
  combinator), `BMux`, `BSelect`; scalar reads `BGet`, `BTotal`, `BCount`; `SigK` (signal
  constants) and `Each` (comprehension placeholder). Constant terms fold; `g.mux` routes bundles.
  Constants are `Cv` (int, bundle or signal) everywhere (consts, prologue, consteval).
- **Comprehensions** (bundle.rs): `v` lowers to `Op::Each`; the scalar expression is then
  converted to bundle operations over a *domain* (the input's signals passing the filter),
  where every intermediate bundle holds a subexpression's value with missing = 0. Operations
  that keep 0 at 0 (or apply to `v` itself, never 0) are one `Map`; others add the domain
  explicitly (`Zip` with the scalar spread over the domain). Selects restrict the domain.
  Conditions on `v` are decider literals; conditions on other expressions compare their
  bundle with 0 in a `DFilter`, whose `each` iterates the domain (green) and the bundle (red),
  so signals missing from the bundle are tested as 0. `//`/`%` truncate per signal.
- **Types**: `Ty::Bundle`; un-annotated bundle variables are inferred syntactically to a
  fixpoint (`bundle_names`); assignments, `if` merges and selects check kinds.
- **Codegen**: a bundle value is a `BRef` with its own wires, created per colour on first read
  and connected to all producers at the end (`bfinish`); bundle combinators read the bundle on
  red and numbers from the bus on green (never both on red: user bundles may contain any
  signal, including the compiler's own). Bundle registers: hold decider (`everything` copy
  from red while no load) plus `each * enable` loads; samples likewise. Pipelined blocks delay
  bundles with `each + 0` combinators.
- **Layout**: bundle wires can join distant entities (ports at the edges), so long hops go
  through relay poles placed greedily on free tiles.

### Tooling
- `--set stock=iron-plate:5,copper-plate:3@10`; `sim` prints bundles as `{name=value,…}`.
- The in-game harness sets bundle injectors slot by slot and records bundle outputs from
  `signals_last_tick`; difftest compares canonical strings.
- `tools/fuzz_bundles.py`: random bundle expressions/comprehensions in `every tick`,
  `every 20 ticks` and main-loop programs against a Python model of `each` semantics.

### Status
- New examples `requester`, `inventory`, `deliveries`, `bundles`; all difftest-match the game.
- Fuzzer: 300 programs, 0 mismatches.
- Not yet: `argmax`/`nth`, runtime `Signal`, `for s, v in b.items():`, quality.
- Cost: pipelined blocks give every output its own register; outputs that are pure functions
  of the inputs could skip it (and its delay taps). Worth doing with the layout work.

## 2026-10-09 — Optimisations: register-free outputs, step fusion, late scheduling

Measured with `tools/bench.sh` (combinators per example; before → after):
inventory 70 → 52, math 127 → 95, deliveries 41 → 33, requester 11 → 6, bundles 66 → 61,
demo 30 → 28, arrays 182 → 179; calculator and primes +2 (step copies) but faster.

- **Register-free outputs** (codegen `combinational`): an output of an `every tick` block that
  is assigned once, unconditionally (or constants under conditions), and read by no process,
  needs no register: the output port reads the pipeline. Constant-under-condition outputs
  (bools, `x if c else k`) become one decider per constant. When other states of the block
  still use registers, these outputs are taken one tick later so an iteration's outputs
  still change together; otherwise the warm-up taps aren't needed at all.
- **Late scheduling** (pipeline.rs): input-only values can be computed as late as possible,
  so alignment delays sit on the inputs (shared by every consumer) instead of on each result.
  Both schedules are costed in delay combinators and the cheaper one is kept (late scheduling
  loses when one result has many consumers, e.g. arrays).
- **Step fusion** (cfg.rs `fuse`): `A; goto B` merges into one step when B doesn't wait; B is
  copied if it has other predecessors and is small (≤ 6 statements). Steps rarely end in a
  plain jump (loops are rotated, straight code is already one step), so the gain is in
  runtime: calculator 786 → 752 ticks, primes 801 → 717.
- **Fix**: a variable is inferred `bool` only if every assignment is syntactically boolean.

Where the time goes now: a step lasts its logic depth + 1 tick (the register), which is
already the minimum for register-based steps; loop iterations are bounded by the depth of
their loop-carried calculation. Further: if-conversion of branch targets (merge a branch's
simple successor into the branching step), register sharing, real placement.

### `--outputs=west` (2026-10-09)
Output ports sit at the west edge north of the blueprint, one row each (first output
northernmost), facing west. The combinator that used to be the port becomes a gate
(`Role::OutputGate`) on the east edge; its result runs on its own line of poles (red) to the
port, a pass-through (`x + 0` / `each + 0`). +1 combinator and +1 tick per output.

## 2026-10-09 — Experimental placement by simulated annealing (`--place=anneal`)

Opt-in (`place.rs`); the grid stays the default. Internal combinators are assigned to 1×2
slots (columns skip every 7th tile column when there are power poles); ports, gates and the
RUN switch stay where the grid layout puts them. Cost: footprint (or the free side under
`--max-width`/`--max-height`, which apply to the whole blueprint), a gravity pull of every
entity towards the ports' corner (without it only edge entities feel the footprint, and
the result was worse than the grid), per-network half-perimeter plus a heavy penalty for
spanning-tree hops beyond reach (networks ≤ 16 members), and a centre pull for big networks
(bus, cluster wires). Starts from the serpentine order, fairly cool; moves are swaps within
a shrinking window; `--seed` and `--effort`. Remaining long hops get relays as usual.

Measured with `--no-poles` (whole blueprint, grid → anneal): calculator 28×14 → 25×14,
stats 35×26 → 36×22, arrays 28×20 → 29×16, inventory 21×9 → 17×10. The annealed blocks are
85–95% dense already, so most of the gain is the pole columns the grid leaves empty even
without poles. Bigger wins now need: rotated (2×1) combinators, filling the return-line
region north of the blueprint, and packing the return lines themselves. Difftested in-game
(calculator, inventory with west outputs, stats with --max-width 24): all match.

## 2026-10-09 — Level 4: signal arrays; quality signals inside

### Verified first (probe scenario, `L*` and `Q*` rows; simulator test `arrays_match_the_game`)
- Read: `each(green) == I(green)` with the output copying red onto one signal sums the one
  match; the index signal itself also matches (`I == I`) but the array has no `I`.
- One-hot `each(red) == I(green) → each = 1`; mask `each(red) != 0 ∧ each(green) == 0`.
- `each >> 1 → X` is an arithmetic shift, summed; the selector ranks by index (nothing past
  the end) and sums both wires.
- Quality (`TICKY_SPACE_AGE=1`): every quality of a signal is a separate signal for `each`,
  `everything`, selectors, conditions, outputs and constant combinators; blueprints add
  `"quality": "…"` to signal IDs.

### Signal arrays (expand.rs `Shape::Mem`, ir.rs `aget/aset/aadd/azeros/amax/asorted`)
- An array indexed at runtime anywhere (or longer than 256) is a bundle per bank, element `k`
  on `Graph::slot(k)` (the internal pool minus the index signal). The expander records runtime
  indexes per name (call numbers stripped: `f.3.xs` → `f.xs`) and re-expands until nothing
  new turns up (≤ 6 rounds); only names, never values, decide: a signal array assigned to an
  unmarked name is read out element by element (an early version spread signal arrays into
  `stats`' sort function and serialised its swaps: 117 ticks deep).
- New IR: terms `Shift` (`x + k → sig`, index wires), `Hot` (one-hot), `Fold`
  (`each op k → sig`); ops `AGet` (array read), `BSelect` with a rank. A read is 2 ticks; a
  write 3; `+=` 3 without reading.
- `sorted`: keys `2x + 1` (a Map plus a constant on one wire), N ranked selectors, N
  `each >> 1 → T[k]`. `min`/`max` use the selector on the nonzero elements and fix up zeros.
- `index`/`in` count matches with a comprehension, plus zeros (`azeros`) when the value may
  be 0.
- Bundle `a + b` of small computed bundles merges their terms onto one wire (no combinator).
- Results (combinators): arrays 179 → 59, stats 307 → 184. New examples `sorting` (§15.9)
  and `histogram` (§15.12, includes a two-bank array).

### Quality signals inside (default; `--no-quality` to turn off)
The internal pool is the base pool × uncommon…legendary (1432 signals), set per compilation
(thread-local `set_quality_pool`). Quality variants are separate `Sig`s (`with_quality`,
`display` → `signal-A@rare`). The harness loads the Quality mod (`TICKY_QUALITY=1`, set by
`difftest`). All 22 examples difftest-match the game with quality inside.

### Fixed: evaluation order around calls that change globals (pre-existing)
`b = a + f()` where `f` sets global `a` gave 11 instead of 2: calls are hoisted before the
expression but earlier operands were read after them. Now values are frozen into temporaries
when a later operand calls a function that writes module variables (`impure_fns`,
transitively); `t op= f()` reads `t` first; `xs[f()] = v` evaluates `v` first. Found by
`fuzz_level2.py` after the array changes, reduced with the new `tools/reduce_level2.py`.

### Annealing fix (2026-10-09, reported on enf: anneal 1435 tiles vs grid 1260)
The annealer's slot grid had ~40% spare slots; the wire terms (which dropped 10×) outweighed
the footprint term and the block spread out (histogram's footprint term 266 → 352). Now the
grid is tight (5% spare), the footprint term is the whole blueprint's (port columns and
output lines included: `Frame`), and `layout` anneals three block shapes (the grid layout's
width with exact rows, the best area within 2:1, a square block) and keeps the smallest.
Annealing is never larger than the grid now: `--no-poles --outputs=west` saves 9–14%
(enf 1260 → 1120, sorting 1116 → 957); with poles the pole columns fix the width, so it
ties the grid's footprint and saves relays.

## 2026-10-09 — Level 5: processes and `--checks`

### Processes (`process name:`, SPEC §9.2)
- Parsed already; now each `process` (and `main`) is a `MainProc` in `Program::procs` with its
  own owner id (`proc_owner(k)` counts down from `MAIN`), state machine (PC, step timer,
  ANY), samples and subroutine return registers. ST pulses every process's ANY.
- **Own variables.** After the prologue is known (program.rs), names a process assigns that
  have no prologue value and aren't ports are renamed `P:x` throughout its body and its
  subroutines. Only prologue variables (and outputs) are shared, so `main` and processes can
  all use `i`; anything else could not legally be read by another process anyway. Display:
  "`x` in process `P`"; reading another process's own variable says whose it is.
- **Subroutines per process.** The expander namespaces subroutines by process (`P:f`, locals
  `P:f.x`), so every process has its own copy (its own return register and locals).
- Fixed on the way: the expander's module constants ignored assignments inside processes,
  so `z = 1` in `main` turned a process's own `z` into the constant 1 (found by the fuzzer).
- `tools/fuzz_procs.py`: 2–3 processes (sometimes `main`), each a random program from
  fuzz_programs over its own a, b, c, chained by "result, then flag" handshakes; Python runs
  them in order. 160 programs, 0 failures (after the fix). handshake (§15.10) matches the game.

### Runtime checks (`--checks`, SPEC §13)
- Thread-local `checks_on()` (like the quality pool). Hooks: the expander turns `assert e`
  into a statement (dropped without `--checks`), adds `assert #ixok(i, n)` before runtime
  writes and wraps runtime reads in `#chk(i, n, read)`; lowering records `g.check(fail,
  span, what)` for those and for `//`/`%` (also `//=`/`%=`) by a divisor that may be 0.
- **Path conditions** (`Graph::path`): `if` branches, `x if c else y` and the right side of
  `and`/`or` push their condition, and a check's failure condition is ANDed with the path, so
  `x // y if y else 0` never fails. Constant-false checks vanish by interval/constant folding.
- **Steps**: checks are fused (`fused_checks`) and read by the commit decider (`fail == 0`
  for each, which also gates the guarded-load enables) one tick before the commit, so a step
  with checks may be one tick longer. One error decider per check (same timing conditions,
  `fail_k != 0`, earlier checks passing, `ERR == 0`) loads the code into ERR and pulses ANY
  without a commit: PC drops to 0 (halted). ERR is one hold decider; codes are numbered
  blocks first, then processes in step order, and listed in the build report.
- `every` blocks: checks force multi-cycle (no pipeline); error deciders fire with the commit
  pulse's conditions; the block keeps running.
- Error lamp (`Kind::Lamp`, `Role::ErrorLamp`, beside the RUN switch, on the bus; blueprint
  format dumped from the game with the `lampdump` scenario: `circuit_enabled`,
  `circuit_condition`, `color`) and a synthetic `error` output port (signal-E). The harness
  now writes lamps' states (`lamps.txt`): off before, lit after a failure, in-game.
- In constant expressions a failing check (division by zero) makes the expression non-
  constant, so it runs (and fails) at run time; a constant assert that fails stops the
  prologue the same way.
- `CHECKS=1 tools/fuzz_programs.py`: Python raising ZeroDivisionError ⇔ the circuit's error
  output nonzero, otherwise identical values and error 0: 200 programs, 0 failures.
- Example `checks` (first line `# ticky: --checks`, which tests/examples.rs honours) matches
  the game, including a block division by zero, an assert and a RUN reset.

## 2026-10-09 — Level 6: runtime signals, bundle iteration

### Verified first
- **Selector ties** (scenario `tieprobe`): deterministic and independent of slot order;
  `select` max ranks equal values items < fluids < virtual, each in prototype order (our
  table's order within a kind), then by quality; min is exactly max reversed. The simulator
  used signal-table order (virtual first) and the same order for min: fixed with
  `SignalTable::rank`, also used when folding constant ranks. Test
  `selector_ties_match_the_game`.
- **Selector with an index signal** (scenario `selprobe`): the index signal is read and takes
  no part in the ranking; missing = 0; past the end, nothing. New `Selector::SelectAt`. The
  selector reads both wires, so the index sits on its own wire (a `Shift` term), never the bus.
- **Lamps** (for `--checks`) and quality output signals in bundles: in the examples below.

### Runtime `Signal` values
- A runtime signal is a one-hot bundle; `Op::SigOf(b)` marks it for typing only (a user's
  `Bundle(iron=1)` constant is the same node as the signal `iron`, so the mark can't live on
  the node). Every consumer unwraps (`Graph::unsig`); `SigOf` never reaches fusion or codegen
  (`locate` looks through it anyway). Signal-typed sources (`src_sig`) are bundle registers.
- New IR: `BDot(a, b)` (`each(red) × each(green)` summed onto one signal: `b[s]`, `s in b`),
  `BSelectAt(b, max, ix)`, `onehot` (filter `each != 0 → each = 1`), `bset_dyn` (domain filter
  "where `s` is 0" copying `b`, plus `s × x`). `g.mux` selects between signals (runtime or
  different constants) as bundles; `truth` of a signal is "is a signal".
- `bundle::Kind::SigVal`; `Key::{Const, Dyn}` for `b[k]`, `b[k] = x`, `.get`, `in`, dict keys
  (runtime keys are set one by one, so repeats keep the last value).
- `Ty::Signal` (bundle-like: `Ty::is_bun`), inferred syntactically (`signal_names`: `S(…)`,
  `.argmax()/.argmin()`, `#hot`, copies, choices) or annotated; prologue constants become the
  initial one-hot value. `Signal` ports: no `@`; inputs read the argmax of their wire
  (normalised when read), outputs send the one-hot bundle. CLI `--set want=coal`.
- `S(name, quality="rare")`.

### `argmax`/`argmin`/`nth`, bundle iteration
- `argmax()` = `onehot(brank(b, max, 0))`, 2 ticks. `s, v = b.nth(k)` is expanded into a tuple
  of `#hot(#rank(b, k, True))` and `#total(…)`; a runtime `k` uses `BSelectAt`.
- `for s, v in b.items(ascending=…):` / `for s in b.keys():` (sequential code only):
  `rest = b; for k in range(len(rest)): top = #rank(rest, 0, max); s = #hot(top);
  v = #total(top); rest = rest - top; body`. 4 ticks per iteration; `break`/`continue` work.

### Status
- New examples `signals` (every-tick argmax/argmin/runtime nth/value_in, keys() loop, runtime
  dict keys, a rare-quality signal, Signal ports and state), `dispatch` (§15.7: 3 ticks per
  dispatch, 15 combinators), `ranking` (items() loops both ways, nth, `in`, runtime key
  writes); all match the game, including ties across items, fluids and virtual signals.
- `tools/fuzz_signals.py`: random bundles with ties and negatives through loops (both orders,
  break/continue), signal comparisons, runtime-key writes, argmax/argmin and runtime nth,
  against a Python model of the game's order: 150 programs, 0 failures.

## 2026-10-09 — Port rows (`--ports=ew`) and annealed output gates

Reported on enf (56 wide, 20 outputs, `--outputs=west --place=anneal --no-poles`): 56×38
tiles, 209 output-line poles; the N-S port column and its 20 return lines were most of it.
- `--ports=ew`: the RUN switch over the lamp, then the inputs (facing south) along the north
  edge; outputs along the south edge (`--outputs=south`, default) or continuing the north row
  (`--outputs=north`, facing north, no gates or return lines: ports read the bus and bundle
  wires directly). Pole rows above/below the port rows. The annealer's `Frame` got `min_w`
  (the port row); the layout's size is the bounding box of everything in these modes.
  enf: 56×18, 285 combinators (no gates), 3 relays.
- `--outputs=west --place=anneal`: the gates go into the annealed block (turned upright) and
  each gate→port line is an ordinary two-member red network (relays where needed) instead of
  fixed pole lines, so the annealer pulls gates towards their ports. inventory: 54 carrier
  poles → 4 relays.
- Harness: power goes next to the left-most pole *with copper wires* (a relay west of the
  ports left the build unpowered); input injectors for south-facing ports go north of them.
- `Dir::South` (blueprint direction 8).

## 2026-10-09 — Relay routing stays inside the block

Reported on enf (`--ports=ew --outputs=north`): relay poles strung far north of the port row.
Relays aren't annealed; `route()` placed them afterwards with a breadth-first search that took
the first fewest-hop path, ties broken by scan order (north-west first). It's now a Dijkstra
over tiles ranked by (distance outside the block's bounding box, pole cost — reusing a pole's
free connector is cheaper than a new pole — then distance from the straight line). enf at
`--max-width 56 --no-poles`: ew/north 56×18 → 56×14 (3 → 4 relays), ew/south 60×24 → 56×22,
west 59×35 → 54×35.

## 2026-10-10 — Optimisation round: next-PC offsets, priority muxes, direct bundle writes

Measured first (combinators by role): in sequential programs control dominated (calculator:
23 PC-load deciders and 13 commits vs 17 doing arithmetic); in enf (bundle-heavy `every`
blocks) copies and bundle selects did. Before → after (tools/bench.sh): enf 390 → 319
(depth 10 → 6, 152 → 86 signals), calculator 125 → 112, handshake 54 → 43, sorting
298 → 276, primes 55 → 49, every sequential example −3 to −13.

- **Next-PC as an offset** (codegen `main_proc`). The PC hold runs whenever RUN is on (no
  longer dropped by ANY); each commit decider also outputs `PC += fall - here` (goto, call,
  halt, or the branch's else-target), so gotos cost nothing. A branch adds `taken - else`
  one tick later, from `CM ∧ cond` as before, so conditions are still read on the commit
  tick and no step got longer; the transient PC value sits under ANY ≠ 0, when nothing reads
  it. Returns drop to 0 by offset, then add the return address (`ret × CM`) as before.
  Error deciders also drop the PC to 0.
- **Priority muxes** (`Op::BDec`, fuse `barms`): a tree of bundle selects (`if/elif` chains)
  becomes one decider per leaf, each checking its whole path condition as a DNF over the
  original comparisons (≤ 12 terms, ≤ 8 arms) — one stage instead of one per level, and the
  condition deciders vanish. New example `alarms` (two if/elif bundle chains): 80 → 60.
- **Direct bundle writes**: `One(s, x)` with `x` an arithmetic, comparison or decider node
  becomes `BTerm::Ar`/`BTerm::Dec`, which write `s` on the bundle's wire themselves (no
  copy, one tick less; a duplicate if `x` has other users, which costs what the copy did).
- **Key writes** `b[s] = x`: copy + `Set(b, s, x)` = one arithmetic `x(green) − s(red) → s`
  (was copy + `Pick(b, s, -1)` + `One`/constant).
- **Relay routing**: relays reuse their own network's poles; each member joins the nearest
  part of its network's tree (members and relays so far, Steiner-style); a hop that can't
  start falls back to a search around the whole block; a network that still fails is moved
  to the front and everything is routed again (rip-up and reroute, ≤ 8 times). Needed after
  enf's netlist changed and hit congestion in the grid.
- **Known limit**: the default grid layout runs out of relay room on very large programs
  (fuzz programs of ~1900 and ~5000 combinators; both failed before this round too).
  `--place=anneal` lays them out (the 750-combinator one with 2 relays instead of 167).

Verified: all 28 examples difftest-match the game; fuzzers clean (bundles 150, signals 100,
programs 100, CHECKS 80, procs 60, blocks 100, exprs 6900; level2 only the layout limit).

Considered and not done: forwarding bundle reads (`b[s]` → `BGet`, 58 in enf) into their
consumers — almost all feed select guards whose red input already carries the selected
bundle, and each read is already shared, so little to gain.

## 2026-10-10 — Screens (`import display`), write combining

### Verified first (scenario `rgbprobe`)
A lamp in packed-RGB colour mode (`use_colors`, `color_mode = 2`, `rgb_signal`) shows the
signal's low 24 bits (`0x1000000` → black, `-1` → white). Without a condition it's always on
(0 = lit black); with `≠ 0` it's off at 0. Quality signals work as the colour signal. Timing
(difftest): the colour follows the network on the same tick, on/off the tick after; outputs
are read as of the tick before, so the screen columns of a trace use the simulator's next tick
for colours and this tick for on/off (`screen_trace` in the CLI).

### Screens
- Syntax: `import display` (new statement; only `display` exists), then
  `output s: display.Screen(W, H) = port("…")`. `display.rs` rewrites the module before
  expansion: the screen becomes a module variable `s = [0] * (W*H)` (a prologue value, so it's
  shared like a port) that expansion is told to make a signal array (`expand_module(m, mem)`);
  `s[x, y]` → `s[y*W + x]`; `s.fill(c)` → `s = [c] * N`; `s.width`/`s.height` → constants.
  Banks `s#0`, `s#1`, … are kept live (`live_states`).
- Codegen: a lamp per pixel (`Kind::Lamp(cond, Some(sig))`, `Role::Pixel`) on its bank's red
  wire, colour signal = condition signal = `Graph::slot(j)`. Layout (`place_screens`): beside
  everything else on the chosen side (`--display NAME=SIDE`), with pole rows above and below
  (and a pole column for tall screens so the rows join up); sizes use the bounding box.
- Tests read `screen[x, y]` (the value at the lamp's input; `Harness::pixel`); the harness
  writes each screen's colours per tick, and difftest compares them.

### Making screens cheap (also helps every array/bundle program)
- `#arr` (array → bundle): elements with the same value share a term, `ones × x` (`[x] * n`
  is one combinator, not n), constants one constant combinator. `fill(c)`: 132 → 5.
- `bmux_tf` only splits a select of small bundles into per-signal selects up to 8 signals
  (a select between two 128-pixel constants was 260 combinators; now 7).
- **Write combining** (`bset`): a write to a bundle that's already "`b0` copied plus some
  `Set`s" becomes one more `Set` on `b0` (replacing a write to the same signal), so a run of
  constant-position writes is one stage deep instead of a chain (screen example depth 67 → 5).
- **Grouped writes** (fuse `combine_writes`): the `Set`s on one base become one combinator
  that takes the old values out (`b0 × (-1 on the written signals)`, a `Zip`) plus one term
  per distinct value; a value that is constants under conditions becomes `BTerm::Dec`, now
  a decider per arm outputting a constant on *all* its signals (also used for `ones × cond`).
  Screen example 120 → 56 combinators; enf 319 → 309.
- Fixed (pre-existing, found by fuzz_bundles): inside a comprehension, `//`/`%` in parts that
  don't involve the element (`{s: -2 % k …}`) floored instead of truncating as SPEC §4.3.5
  says (`Graph::in_comp`).

## 2026-10-10 — The other selector modes (scenario `qprobe`, Factorio 2.0.77)
Ticky uses `select` (with constant or signal index) and `count`. 2.0.77 also has `random`,
`stack-size`, `rocket-capacity`, `quality-filter` and `quality-transfer` (the wiki's "time"
and "quality select" modes aren't in 2.0.77). The quality modes need the Quality mod. Findings:
- **Quality transfer**, target `each`: every input signal re-tagged to one quality, with
  values of signals that now coincide summed (`iron@normal=100, @rare=3, @epic=5` → `iron@rare=108`).
  Static quality via the API needs a table (`quality_source_static = {name = "rare"}`; a bare
  string is silently ignored, giving normal). From a signal: the highest quality of that signal
  on the inputs, and the source signal is left out of the output; absent → no output.
  Specific target: just that signal, read at its own quality. `anything`/`everything` refused.
- **Quality filter**: passes the signals whose quality satisfies `cmp q` (`=`, `≠`, `<`, `>`,
  `≤`, `≥`), summing both wires.
- **Stack size** / **rocket capacity**: per item, the value replaced by the stack size
  (rocket capacity), quality kept; fluids and virtual signals dropped (rocket capacity also
  drops what can't be launched, e.g. the silo).
- **Random**: one input signal (with its value), uniform-looking; `random_update_interval`
  0 or 1 = a new pick every tick, N = every N ticks; a single input passes through.

## 2026-10-10 — Standard library: `items`, `quality`, `random` (SPEC §8.4 items 6–8)
- `stdlib.rs`: `import NAME` for any library in `LIBRARIES`; before expansion `lib.f(…)`
  becomes the builtin `#lib.f(…)` (expansion passes it through; `lower` calls
  `stdlib::lower_call`). Type inference knows which return bundles/signals.
- IR: `Op::BSel(b, Selector, nonce)`, one selector combinator in any of the new modes (folded
  for constant bundles, except random picks; the nonce keeps two random calls apart).
  Netlist `Selector` gained `StackSize`, `RocketCapacity`, `QualityFilter`, `QualitySet`,
  `Random`; the simulator implements them from the probes (tests `selector_mode_tests`).
- Item data: `ticky-factorio/data/items.tsv` from scenario `itemdump` (a selector reading every
  item at once), base and Space Age columns; `--space-age` picks the column.
- Pipeline fix: a node whose operands are all constants (a random pick from a constant
  table) had no time slot and crashed codegen; it now runs just before its first use.
- Random taint (`stdlib::random_names`): names assigned from random calls, from tainted names
  or function results, or under tainted conditions (to a fixpoint); difftest prints them and
  compares them as `*`. In-game (dice example): rolls 1–6 held for 60 ticks, 0 before the
  first pick; coin 140/150; picks over all queued signals.
- Runtime `quality.set(b, q)`: five transfers + `BDec` guards on `q`, rather than the
  selector's "quality from signal" source (it drops the source signal from the output).
- In-game difftests: warehouse and dice MATCH (dice: random columns skipped).

## 2026-10-10 — Screen drawing (SPEC §8.4 item 1)
- `display.rs`: drawing statements are spliced into their body (`rewrite_body`) as
  `screen = #draw(screen, W, op, …)`, runtime arguments first bound to `_drawN_…`
  temporaries. `number` computes each glyph index arithmetically (digit + 10·blank +
  minus) with `tdiv`/`tmod` (its argument is `abs(n)`), then one table read per glyph:
  an `if` chain was 13 deciders and 13 selects more; floor division's sign fixes 20 more.
- Expansion turns `#draw` on a signal array into `#drawb(bank, offset, length, …)` per bank;
  `display::lower_draw` builds the IR. Known pixels → `bset` (write combining). Otherwise a
  mask per shape: `x + 1` table filtered by the x range → `BIG` (2^16), added to the `y + 1`
  table on the same wire, filtered by the y range shifted by `BIG`. Glyph bit test: `bits <<
  (31 − i)` negative (shift amounts from a constant table, or `31 + 3y + x + 1 − (3py + px +
  1)` at runtime; +1 so pixel 0 is on the wire: found by `screen_drawing`). A call's masks are
  summed on one wire; painting is `old + old·mask + c·(−mask)`, joined to a chain of drawings
  by a `Zip(Add)` (merging terms duplicated every earlier drawing's combinators: 145 → 134).
- Cost (16-wide test screen): runtime rect 19 (block overhead included), text 8, digit 15,
  number width 3 47. Dashboard example: 89 combinators at `every 20 ticks`.
- In-game: dashboard MATCH; a scratch program with runtime-position rects, digits and text,
  clipped at every edge, MATCH (so Factorio's shifts agree with the simulator's where it
  matters).

## 2026-10-10 — Readouts: `display.Digits(n)` (SPEC §8.4 item 2)
- `Screen` gained `var` (the signal array shown; a hidden `_digits_NAME` for readouts) and
  `kind`. A readout's name is an `int` module variable (0 at start); one generated `every`
  block draws all readouts (`fill(0)` then `number`), with the internal period
  `display::NATURAL` (`#natural`): as often as its depth allows, never pipelined, no warning.
- `number` at a constant position (also used by `screen.number`): op 2 of `lower_draw`,
  `number_mask` — every glyph at once from per-pixel tables (place values, leading places,
  top glyph, and per-pixel "which glyphs light me" bits `31 − d`), shifted by the digit with
  a `Zip(Shl)` (a missing digit is 0: still right). Readout 57 → 25 combinators; the dashboard
  89 → 58; the drawing test program 134 → 55. Painting onto a blank bank is one combinator.
- Tests read a readout by decoding its lamps (`display::read_digits`).
- In-game: readouts and dashboard (−2147483648 included) MATCH.

## 2026-10-10 — Panels: `display.Panel` (SPEC §8.4 item 3)
- Probe `panelprobe`: the first message whose condition holds shows; same delay as a lamp's
  on/off; wildcard icons show as the wildcard (not resolved from the wire); blueprint
  `control_behavior.parameters = [{condition, icon, text}]`, entity keys `always_show`,
  `show_in_chart`; the control behaviour only exists once the panel is wired.
- `Kind::Panel` (netlist, blueprint). The panel is a 1 × 1 `Screen` (kind `Panel`, array
  `_panel_NAME`): `NAME = e` → `_panel_NAME = [e]` (a whole-array write: element writes fed
  back through the old bank, period 3), `NAME op= e` likewise, reads → `_panel_NAME[0]`;
  keys → numbers in assignments and comparisons (`panel_keys`), tests excluded from the
  renaming (they read the panel through `TestNames`).
- Harness: a screen whose entity is a display panel reports the index of the message shown
  (matching text and icon); the simulator side uses the previous tick's value. MATCH on a
  scratch program (including a one-tick message) and on the readouts example.

## 2026-10-10 — Speakers: `import speaker` (SPEC §8.4 item 4)
- Probe `speakerprobe`: 12 instruments (alarms … steel-drum) with their notes; ids 0-based (a
  new speaker is instrument 0, note 0; 12 resets to 0); blueprint keys `parameters`,
  `alert_parameters`, `control_behavior.{circuit_condition, circuit_parameters}`; entity
  status says "working" regardless; `circuit_condition.fulfilled` is readable.
- `Kind::Speaker` (netlist, blueprint); `speaker.Alarm` (condition `≠ 0`, global, alert) and
  `speaker.Notes` (pitch from the value, condition `> 0`) are 1 × 1 `Screen`s of kind
  `Speaker` on the panel machinery (generalized: name → hidden array); `tune.play(n)` →
  `tune = n`.
- Harness: a speaker reports its signal's value while `fulfilled`, else 0; both as of the
  current tick (unlike a panel's message, one tick later). Also writes
  `ticky/peripherals.txt`: every speaker's and panel's settings after import (all round-trip).
- In-game: scratch program and `sounds` example MATCH.

## 2026-10-10 — Controls: `import controls` (SPEC §8.4 item 5)
- `stdlib::controls` rewrites `controls.Switch/Setting` ports into `bool`/`int` inputs
  labelled by their first argument and records them (`Program.controls`); codegen adds a
  constant combinator (`Role::Control { port }`) wired to the port's red input; layout puts
  it 1.5 tiles west of the port (north with E-W ports).
- Simulator: `set_constant_values` (a player editing a constant combinator).
  `Harness::set` on a control switches/edits its combinator instead of injecting a value;
  the difftest job lists `control`/`switch` per port and the Lua harness does the same.
- In-game: scratch program and the example MATCH.

## 2026-10-10 — Fixed placement: `at=` / `--at` (SPEC §8.4 item 9)
- Origin: the combinator grid's (0, 0), which every layout uses; so a fixed peripheral's
  tiles are known before placement. `Screen.at` (from `port(…, at=)`), `Control.at`,
  `Options.at` (CLI `--at NAME=X,Y`, wins); `LayoutOpts.screens` carries `at`,
  `LayoutOpts.controls_at` the controls'. A control's wire to its port is now a `NetSpec`
  (relayed when far) rather than a direct wire.
- `layout::reserved_tiles`: a screen with its pole rows (and tall screens' pole column).
  Grid and annealer (`place::anneal(…, blocked)`, grid grown to keep enough free slots)
  skip blocked slots: reserved, or (with poles) no free tile of the segment's pole column
  within reach (|Δy| < 4.5) — without that, a pole moved off a screen left combinators dark.
  Core poles on reserved tiles move along their column (not onto other poles: an early
  version stacked two); a repair pass adds a pole beside any unpowered combinator; MST
  gaps over 9 tiles get chains of poles on free tiles near the line (far peripherals).
- Fixed screens are placed first; automatic ones go around everything placed so far
  (fixed ones included). Errors: two fixed peripherals overlapping (names both), a fixed
  peripheral on the ports/RUN/poles (from `validate`'s overlap, translated); internal
  layout errors now name the entities' kinds and roles.
- Sweeps: dashboard 220 positions × grid/anneal, readouts 72 with three peripherals: no
  failures beyond the expected overlap errors. In-game MATCH: screen inside the grid
  (5, 9), 60 tiles away, annealed (3, 4), readouts+panel mixed, controls far away.

## 2026-10-10: harness scenario `moddump`

`TICKY_SCENARIO=moddump TICKY_SPACE_AGE=1 TICKY_EXTRA_MODS="name=path" harness/run.sh` writes
`ticky/moddump.tsv`: every item, fluid and recipe with the mod that created it
(`prototypes.get_history`, which wants the prototype *type*, e.g. `rail-planner`, not "item"),
its localised_name as JSON, and for recipes the category, ingredients, products and time. It
works for any mod, with no name-prefix filter (the old `names` scenario only did `nt-`). Used
to write the user's `cubium-names.txt` / `cubium-recipes.txt` (Cubium 1.0.28: 13 items,
10 fluids, 82 recipes). Those files are the user's reference, untracked; don't commit them.

## 2026-10-10: Cubium generator, and three compiler fixes it found

`examples/cubium-generator.ticky` (written at the user's request; their own attempt is the
untracked `cubium-copper.ticky`): four crafter rows, each set to one of four Cubium recipes.
In-game difftest MATCH with Cubium loaded
(`TICKY_SPACE_AGE=1 TICKY_EXTRA_MODS="cubium=../cubium"`, `--space-age`), 1499 ticks.
- First draft (rows as `Signal` state, bundle scores + `argmax`, rows deciding in sequence):
  ~880 combinators. Recipes as small ints, one row decided per turn (`rows[turn]`), signals
  only at the outputs: 221. One decision per pass rather than four chained ones is the big win.
- **Fix: `Graph::truth` looped forever** on Signal state/ports (`Op::Src` with `src_sig`):
  `is_sigval` is true but `unsig` returns them unchanged, and truth recursed on the same value.
  `mux` between two such signals recursed the same way; it now builds the `bmux` directly.
  Hit by `x if s else y` with `s` a Signal variable.
- **Fix: `a and b` with different kinds** (`sig and n > 0`) was a "number vs signal" error;
  it's now the `and`/`or` of their truths (a bool), which is what conditions need.
- **Fix: `contains_exit` counted exits to blocks inside the statements.** An inlined
  function's `return` inside `x if c else y` made `flatten` copy all following code into both
  arms; four rows × four such calls hit the 200k branching budget ("too much branching").
  Now only exits leaving the statements count. Bench unchanged for every other example;
  the generator's first draft went 604 → 221 with the final design.
- `NO_SIGNAL = Bundle().argmax()` at top level isn't constant-folded, so it turns the
  prologue into running `main` code (and every later top-level variable becomes main's,
  giving single-writer errors). Wrote `Bundle().argmax()` inline instead. Could fold.
- Seen once, not reproduced after the netlist changed: "internal layout error: no room for a
  wire relay" with the default grid placement on the ~880-combinator draft (anneal was fine).
- SPEC §7 corrected: element writes to module variables need no `global` (as in Python);
  only rebinding does. The old text said the opposite.
- Later: the user found rows can't keep productivity modules (switching to
  `metallic-aggravation`, which takes none, ejects them onto the output belt). Added
  `matter-amplification` (1 e-cube + 10 jelly → 17 jelly, +7 net per charge; productivity
  only applies to the 7) as the main jelly recipe: 41 ore ≈ 8.1 charges ≈ 16 copper, so
  sustainable without productivity. Plain `cube-jelly` only below AMP_MIN = 30 jelly (to
  start from nothing), and is interrupted once there's enough to amplify. 249 combinators;
  7 tests; in-game MATCH 1499 ticks.
- Later still: in game it stalled with ~1500 dormant cubes, 1 energized, ~1500 jelly and no
  copper. Amplify rows (never interrupted while busy, and 20 crafters each) burnt every cube
  past the jelly goal, and nothing kept copper back for recharging; from there the old policy
  even sent two iron rows after the last cube. Rework (tools/cubium_econ.py models the factory
  roughly and reproduces the stall with the old policy; the new one recovers): ROW_SIZE sizes
  the stocks; the copper score counts 2 plates owed per dormant cube; iron only above
  COPPER_FLOOR (and interrupted below half of it); jelly rows stop at JELLY_GOAL or when they'd
  dip into CUBE_RESERVE (allowed only while there's < 50 jelly). Turn period 30 → 40 ticks
  (depth 32). 261 combinators, 10 tests, in-game MATCH 1599 ticks incl. the stall state.
- Still "only recharge and jelly" in game. Loaded the user's autosave headless (copy, symlinked
  mods, /silent-command over the server's stdin FIFO) and traced the controller's port wires:
  it kept choosing plain cube-jelly with 1000-2000 jelly on the warehouse wire. **Compiler
  bug:** `S("cube-jelly", type="recipe")` registered the modded name first, and the signal
  table's by-name index is first-wins, so every later plain `"cube-jelly"` (`warehouse[...]`,
  test inputs, `--set`) meant the *recipe*: the controller read jelly as 0 forever. Tests and
  the difftest passed because their inputs went through the same lookup. Fix: plain names go
  through `SignalTable::lookup_plain`/`lookup_untyped` (a modded non-item/fluid/virtual signal
  is only found with its type; else the item is interned), and a later item/fluid/virtual
  takes over the by-name entry. Test `modded_item_and_recipe_share_a_name` (fails before).
  Bench identical.
- Probe `recipeprobe`: "Set recipe" takes the recipe signal even at 1 against item signals at
  50 and against the machine's own "read ingredients" on the same wire (so that's no hazard).
- The user's real setup: rows of 6 `advanced-assembling-machine-returns` (working count on
  signal-A..D), an aai-warehouse. At the autosave everything was dormant with 0 copper.
- **Caution:** the user's running game got SIGTERM ~1 min after the headless server with
  their full mod set (SteamAppId=427520) started; cause unproven. Don't run their save
  headless while their game is up without asking.

## 2026-10-11: optimisation pass (cubium-generator 263 → 155, all examples −6%)

User asked for compiler-side savings rather than hand-tuned programs. Tools: `TICKY_DUMP_IR=1`
prints each block's logic graph (codegen `logic()`); combinator descriptions say what made
them (tally them from the blueprint JSON). Measured breakdown first by ablation (turns, share
penalty, scoring maths). Changes, in order, each verified with all example tests + bench:

- **Ranges under conditions** (ir.rs `facts`/`iv_under`/`Iv::restrict`): a select's arms are
  narrowed by their conditions (`intern_hint`), and `floor_div`/`floor_mod` use the lowering
  path's facts (`g.path`). Drops floor corrections after clamps/max(1, …). Wire inputs stay
  FULL, so `1000 - jelly` can still overflow and keeps its correction.
- **Wire sums** (codegen `logic`: `fold`, `transparent`, `absorbable`): `Add/Sub` trees and
  `* const` push into single-use operands, which write the sum's signal with a factor `m`
  (Cmp → dec_const m, Dec arms × m, const-arm selects × m, `Mul` by const scaled, `Sub`
  swapped for −1, `Div` by −k for −1, reads `each * m`). Only in `logic()` (step/period
  blocks, read after settling); pipelined blocks have their own emitter and are untouched.
- **Zero arms**: `Graph::operands` leaves out the condition of a select arm worth 0 (the
  value doesn't depend on it). The pipelined emitter had to skip such arms too.
- **Inlined conditions** (`inline_cond`): a Cmp/one-term Dec used only for constant arms (or
  a gated arm) isn't built; the arm's decider tests it. `eff_operands` rewires consumers.
- **Table lookups** (fuse `table_lookups`): Bun of one-hot Dec arms all testing `x == c_i`
  (Ne-literals implied) → `Hot(table, Shift(index, x, k))`, from 3 arms.
- **Count over slots** (fuse `count_sum`): ≥3 `b[s_i] == k` (same b, const k) in one sum →
  `BTotal(DFilter(ones on s_i, b, each == k))` (domain-restricted, so extra signals on b
  don't count; missing ones read 0 so k = 0 works).
- **Running max** (fuse `argmax_chain`/`argmax`, also from `split` for register loads):
  `best, top = B0, T0; if s_i > top: best, top = K_i, s_i` (≥3, strict >, T0 ≥ 0) →
  scores on internal-pool signals sorted by `rank` (tie order = candidate order), Filter
  `> T0`, `brank` max, DFilter of a `K_i - B0` table, total, `+ B0`. examples/bestof.ticky
  tests ties, floors and "no winner".
- **Gated selects** (`gate`): `x if c else …` with `x` single-use: `x` is computed onto the
  select's own (bus-allocated, reserved in the cluster pool) signal on the cluster wire and a
  decider passes it (`DOut copy, nets RED`). One gated arm per select (two would share the
  name on one wire); the select is forced onto the bus (else it would feed itself).
- **Direct bundle reads/writes**: `One`/`Shift` terms read a single-use `BGet` from the
  bundle's wire; a scalar used only as `One(s, x)` writes `s` onto the bundle's wire (gated
  ones pick `s` as their private name). Reads write a cluster wire via `OutRed`
  (`emit_from_bundle(out_net)`), never a bundle's.
- Verification: fuzzers clean after each stage (note: the fuzzers default to
  `./target/debug/ticky`; always pass `TICKY=` a frozen release copy — earlier runs this
  session had silently tested a stale debug build); 35/35 in-game difftests MATCH after the
  first seven changes and 37/37 (incl. bestof ties and the generator with Cubium loaded) on
  the final build; a deep fuzz run (105,800 expressions, 1,100 programs) was clean; test
  `optimizations_apply` pins the small probe at ≤ 41 entities.

## 2026-10-11: codegen/ and fuse/ split into modules; tools/verify.sh

Pure reorganisation (moved code, visibility, imports; blueprints of every example
byte-identical under `build --json`, `--opt size --checks`, `--place anneal`, `check` and
`TICKY_DUMP_IR`), so concurrent compiler work lands in separate files:

- `codegen/mod.rs`: shared types/helpers, `Cg` core (`alloc`, `core`, checks), `Shared`,
  live/combinational states, top-level `codegen()`. `logic.rs`: `Cg::logic` (step/period
  logic: clusters, gating, `inline_cond`, wire sums, selects). `pipelined.rs`: every-tick
  blocks (`at_ref` delays). `period.rs`: `every N` clocks, EI/ES pulses (extracted from
  `codegen()` as `period_block`). `procs.rs`: `main_proc` step machine. `registers.rs`:
  `register`/`bregister`, samples, `counter`, `warm`, `accumulator`, `Writer`. `bundles.rs`:
  `BVal` wires, `emit_bundle`, `emit_from_bundle`. `ports.rs`: input/output ports, screens.
- `fuse/mod.rs`: plan types, DNF helpers, `Fuser` core (`dnf`, `rebuild`, conditions).
  `plans.rs`: `plan`/`split`/`writer_plan`. One file per pattern rewrite: `lookups.rs`,
  `counts.rs`, `argmax.rs`, `writes.rs` (`combine_writes`). New rewrites: a new file with an
  `impl Fuser<'_>` block, hooked in from `rebuild` (or `split`).
- `tools/verify.sh`: release build, frozen copy of the binary in a temp dir, `cargo test
  --release`, `tools/bench.sh`, and every `tools/fuzz_*.py` with `TICKY=` that copy
  (`FUZZ_N`, default 20; `FUZZ_SEED`, default 1; `BENCH_OUT=file` keeps the bench table).
  Non-zero exit on any failure; ~40 s at the default size. `tools/bench.sh` now ends with a
  TOTAL line (combinators, steps, summed tile area).

## 2026-10-11: IR algebraic rewrites (examples 2254 → 2171 combinators, −3.7%)

Exact rewrites at node construction (ir.rs, lower.rs), so both emitters get them:
- **Shared term out of a select** (`Graph::mux_factor`, from `mux_tf`; `mux` now ends in
  `mux_tf`): arms `x ± d` / `x`, or `x + d1` / `x + d2`, become `x ± (d1 if c else d2)`. Exact
  with wrapping. The new sum's interval is narrowed in place to the select's (`op_iv`, split
  out of `intern_hint`), else `r + (b if r < 0 else 0)` from `floor_mod` would lose the
  `[0, b)` bound and later floors would grow corrections. Skipped for nodes using `Each`
  (comprehension lowering matches select shapes). Biggest wins: sorting 261 → 231, math
  94 → 78, counters 43 → 38, screen 59 → 53, functions 79 → 74.
- **Mul-then-floor-div** (`floor_div`, before the shift case): `(x * c1) // c2` with `x`'s
  range (under the path facts) proving `x * c1` fits: `c1 | c2` → `x // (c2/c1)`, `c2 | c1`
  → `x * (c1/c2)`. Cubium's `ore_score` (`* 1000 // 10000` of 0..20000): 153 → 151. Its
  `jelly_need` doesn't fire: `JELLY_GOAL - jelly` is a wire input, unbounded above.
- **Compare a select** (`Graph::cmp_select`, both operand orders): if intervals under one
  arm's condition decide that arm's comparison, and the other arm's comparison agrees under
  that condition, the select goes (`max(x, lo) > hi` → `x > hi`; clamp's second test now
  reads `x`); if both arms decide, it's a constant or the condition. Interval decisions moved
  to `decide()`. inventory 49 → 46, cubium 155 → 153, dashboard, histogram, math −1.
- **Shift chains** (`ar`): `(x >> j) >> k` → `x >> (j + k)` when below 32. thermostat's
  `smooth // 4` of `(…) // 4`: same count (the inner value is state), one stage shallower.
- Looked for more with an IR-pattern scan of all examples: the 16 `(x * k) % 41`-style nodes
  (sorting's PRNG, guess) have FULL-range `x`, so nothing exact applies. Sorting networks'
  min/max pairs could use `hi = a + b - lo` (exact with wrapping), but `a`, `b` are shared, so
  that costs the same without codegen help; not done.
- Verification: no example grew; `cargo test` (new `algebraic_rewrites`, 47 → 40 entities);
  fuzz_exprs 2×4,600, fuzz_programs 2×300, fuzz_blocks 2×300, fuzz_procs 2×200,
  fuzz_bundles 2×300, fuzz_signals 2×200, fuzz_level2 2×100, plus an ad-hoc fuzzer of these
  shapes (bounded `%`, clamps, `* c1 // c2`; `every tick:` and `every 30 ticks:`) 12,880
  expressions: 0 mismatches. One fuzz_level2 program hit "no room for a wire relay"; the
  baseline binary fails it the same way (the layout bug noted 2026-10-10). Not difftested in game.
## 2026-10-11: front-end optimisations (expand.rs, cfg.rs)

Part of the optimisation campaign (branch `opt/frontend`). Bench: calculator 112 → 109,
fib 33 → 32, functions 79 → 74, primes 49 → 47, ranking 107 → 105, signals 99 → 98, others
unchanged (2254 → 2240, −14).
- **Single-call subroutines are inlined.** `Expander::sub_sites` counts call sites per
  `sub_key` (so per process) in each expansion round; the next round inlines those with one
  (`inline_once`). Round 0 always runs and compiles every one as a subroutine, and the count
  doesn't depend on that choice. The inlined body is the ordinary inlining path (frames,
  exit label for `return`, waits and loops inside work as in `main`).
- **Private loop variables.** `count_reads` counts reads of every name in the module (ports,
  `global`, tests count); a range loop's variable whose reads are all inside the body (for a
  function local: within that function) and which the body doesn't assign becomes `#i{id}.k`
  (displays as `k`), aliased in the body. `cfg::for_range` uses such a `#…` target (also the
  `for x in xs` / bundle-loop index temps) as the counter itself: no `k#k` register, no copy.
  A name read nowhere (`_`) may be assigned by an inner loop; it's private without the alias.
- **Countdown.** A private variable the body doesn't use, `range(n)` (start constant 0,
  step 1, end not constant): the counter starts at `n` and counts down to 0, so `n#end` goes.
  Only start 0: with another start `n - start` can overflow where the original can't.
- **`--opt=size` step copies.** `cfg::fuse` copied small steps (≤ 6 statements) into some of
  their plain-jump predecessors; that saves those paths 2 ticks but adds code. Under size it
  copies only when every predecessor is a plain jump (the step goes). `crate::opt_size()`
  (thread-local like `checks_on`). Under speed it would save calculator/primes 2 each, at
  +7%/+11% ticks in their tests, so speed keeps the old rule.
- Tried, no gain: `Goto` instead of the pre-loop test for statically non-empty ranges (+1 in
  sorting, sounds: `fuse` then copies the body); breaking out of `while` via the loop test
  (hand-written on primes: same count, slower).
- Fuzz (TICKY = frozen release), final build: procs 400, programs 500, level2 300, blocks,
  bundles, signals 300 each, exprs 300 rounds; plus about as many on earlier builds of this
  branch: no new failures. Pre-existing, same on the base
  binary: level2 "too much branching" / "ran out of signals" / "no room for a wire relay"
  compile failures on big programs, and one fuzz_programs false positive (`c *= …` overflow
  that its Python model doesn't flag). Test `single_call_inlining_and_loop_counters`.

## 2026-10-11: register sharing (liveness)

- `liveness.rs`: per-process liveness over the steps (`cfg::Cfg`, with `successors`, so a
  return flows to every caller's continuation), statement by statement inside a step. Two
  variables interfere when one is assigned while the other is live after the assignment (or
  in the same tuple assignment), or both are live on entry (one start pulse loads both). A
  copy `x = y` doesn't make `x` interfere with `y` (loop variable `k = k#k0` shares the
  counter's register). Greedy colouring per class (int, bool); program.rs `share_registers`
  renames the members to a representative in the cfg before `lower_main`; the others become
  states nobody reads, which codegen already gives no register.
- Candidates: the process's own Int/Bool states, not ports, not mentioned by any other
  process's or `every` block's code. Prologue variables qualify too (when no one else reads
  them): the member live on entry is the representative, so the register starts with its
  value. Left out: variables never read across a step (no register, merging would only add
  loads: sorting went +14 before this rule), names in a call's function position, and any
  variable without an initial value read where it might not be assigned (live on entry or
  outside `definite_assignment`), so a merge can't hide that error (test
  `registers_are_shared`).
- Bench: calculator 112 → 102, primes 49 → 47, ranking 107 → 104, functions 79 → 77;
  nothing else changes. `TICKY_NO_REGSHARE=1` turns it off, `TICKY_DUMP_REGSHARE=1` prints
  the merges. About half the programs of fuzz_programs/fuzz_procs/fuzz_level2 share
  registers; fuzzers clean (level2 compile failures: the same layout/signals/branching ones as
  before). In-game difftest MATCH: calculator, primes, ranking, functions.
## 2026-10-11: select stages (codegen/selects.rs): passes, flattening, several private wires

Replaces the "gated selects" and `inline_cond` of `logic()` with a planner
(`selects::plan`). Every select not flattened into another is a **stage**: one combinator per
distinct output, each testing its whole condition (merged arms are OR'd, arms being mutually
exclusive). Outputs: a constant, `Pass(x)` (x computed onto the select's own signal on a red
wire, copied by `DOut copy, nets RED`) or `Mul(x, c)` (the old `x * c`, for an arm value used
elsewhere).
- **Passes** may also be read by the stage's own (inlined) conditions: `max(x, K)` = 2
  deciders (`x ≥ K → copy`, `x ≤ K-1 → K`), `x if x > 0 else 0` = 1. Reads (`BGet`, totals,
  counts) can be passes too.
- **Flattening**: a select used only inside the stage (as an arm, or read by its conditions)
  is absorbed. Arms nest (`c ∧ d → …`); a condition reading an absorbed `Mux` is split by the
  `Mux`'s arms with the value substituted (zero arm: the negated other guard), so a clamp
  `min(max(x, lo), hi)` is 3 deciders: `x ≥ hi+1 → hi`, `x ≤ lo-1 → lo`, `lo ≤ x ≤ hi → copy`.
  Term simplification folds constant literals and tightens each value's comparisons against
  its interval (`g.iv`), dropping false terms and implied literals (a term never becomes
  empty: it keeps one of its own literals, since a decider needs a condition).
- **Several passes per stage** (`x*5 if c else y - x`): the first shares the cluster's wire;
  every other gets a red wire of its own (`own_wire`), and every other value its deciders read
  moves to the bus (`force_bus`). A decider has one red input, so a decider reading two passes
  is a conflict; the planner chooses which pass gets the cluster wire, else drops the pass
  most read by other deciders.
- Planning bans (absorb / pass / inline) and replans until consistent; caps: 64 arms, 48
  literals per decider while flattening. After planning, `logic()` keeps only producers still
  reachable through the wired operands (flattening leaves some values unread).
- A select can be another stage's pass if it passes nothing itself.
- Results: cubium-generator 155 → 141, dashboard −1, bundles −1, histogram −1, nothing grew.
  The random-expression fuzzer only uses `every tick:` (pipelined, not this code); a variant
  with `every 30 ticks:` and clamp/nested-select/shared-operand shapes (2300 expressions) was
  clean, and 48 random 20-output blocks compiled smaller or equal output by output.
- In-game: a probe (max of a computed value, clamp, positive part, two passes on two wires,
  nested select; INT_MIN included) MATCH 259 ticks. Test `select_stages`.
- **Floor `//` and `%` by a constant** (`logic.rs`: `floor_groups`, `emit_floor`): the lowering
  gives `q - [r < 0]` and `r + k·[r < 0]` (Div, Mod, comparison/condition: 3-4 combinators).
  Instead, with c = [a < 0]: `a // k = tdiv(a + c, k) − c`, `a % k = tmod(a + c, k) +
  (k − 1)·c` (k < 0: c = [a > 0], `a − c`, `k + 1`); checked exhaustively over small values,
  random ones and the ends of the range (INT_MIN + 1 can't overflow). One decider reads `a`
  from the bus and writes ±c onto `a`'s own signal *on the results' private wire* plus the
  corrections onto the results; the divider(s) read `a` with both colours (bus value + the
  correction). So `//` is 2 combinators, and `//` with `%` of the same dividend 3. Needs: the
  dividend on the bus (forced), its signal reserved on that wire, the results local (or a
  pass; wire sums allowed, factor ±1 for `//`, 1 for `%`), one group per dividend (two would
  add their corrections). No different-signals-to-different-nets output was needed: both
  outputs go to the private wire, and only the dividers read the dividend's name there.
  cubium-generator −1, guess −1 (most other examples' divisions write bundles or are
  pipelined). Test `floor_division_by_constant`; in-game probe (both signs of k, `//` and `%`
  of one dividend, a floor result as a select's pass, INT_MIN/INT_MAX) MATCH 199 ticks.

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

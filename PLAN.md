# Compiler roadmap: fancier optimisations

Ten features, tackled one at a time in this order. Each one ships on its own (own branch,
merged when done) and must leave every example and fuzzer passing.

## Definition of done (every feature)

- [ ] Measure first: `tools/bench.sh` table saved before starting (`BENCH_OUT=before.txt
      tools/verify.sh`), so the gain is a number, not a feeling.
- [ ] Unit tests for the new pass, plus at least one example or test pinning the win
      (like `optimizations_apply` pins entity counts).
- [ ] `tools/verify.sh` clean (release build, `cargo test --release`, bench, every fuzzer
      against a frozen binary); a deeper fuzz run (`FUZZ_N=200`) for passes that rewrite logic.
- [ ] A fuzzer extended or added if the feature opens new shapes the existing ones don't hit.
- [ ] In-game difftest (`harness/difftest-examples.sh`) when the emitted logic changes. It
      runs headless Factorio, so **ask first**: never while the user's game is open.
- [ ] Bench before → after recorded in a dated NOTES.md entry, including what was tried
      and rejected.
- [ ] Off by default only if it can lose (then a flag, documented in README and `--help`).

## 1. Straight-line vectorisation (SLP) — size

**Status (2026-10-14): merged.** aes128 336 → 281, nothing else changes (little to pack
elsewhere). Open: comparisons true at 0 or with mixed constants; zips (`a_i op b_i`); lanes
reading registers/inputs. In-game difftest pending.

Independent scalar ops of the same shape (`a = x + 1; b = y + 1; c = z + 1`) each cost a
combinator today. With their operands on distinct signals of one wire, one `each` combinator
does them all. We do this for comprehensions (`expand/vectorize.rs`), not for loose code.

- [x] Survey: dump IR (`TICKY_DUMP_IR=1`) over all examples and count groups of isomorphic,
      independent ops in one block (same op, same constant or same per-lane operand shape).
      Decide whether the pass lives in the IR (ir.rs) or the fuser (`fuse/`).
- [x] Packing rule: lanes need distinct signals on a shared wire, and outputs consumed per
      lane must be readable back (direct bundle reads already exist). Cost model: pack only
      when combinators saved > the extra reads/filters it costs.
- [x] Ops to cover first: `+ k`, `* k`, `/ k`, comparisons against a constant (decider
      `each`), then mixed constants via a constant-combinator lane table (`each op each`).
- [x] Pipelined (`every tick`) blocks have their own emitter: cover them or exclude them
      explicitly.
- [x] New fuzzer or `fuzz_exprs.py` mode generating parallel independent assignments.

## 2. Translation validation — enabler

**Status (2026-10-15): merged.** Found and fixed two miscompilations. Open: comprehension
conditions with `v` on both sides / a runtime scalar still subtract (can wrap).

Prove rewrites correct with a solver on 32-bit wrapping arithmetic instead of trusting
fuzzers alone, so the aggressive passes below (3, 4) are safe.

- [x] Pick the solver route: z3 via the `z3` crate (build dependency weight?) or emitting
      SMT-LIB to an external `z3`/`cvc5` in a test-only tool. Prefer test-only: the compiler
      binary shouldn't need a solver.
- [x] Encode the IR expression language (wrapping add/mul, Factorio's division and modulo
      semantics, shifts, comparisons, selects) as bitvector terms.
- [x] Check mode: for each block, the IR before and after optimisation are equivalent for all
      inputs (within the range facts the passes assume). A `TICKY_VALIDATE=1` or a test
      harness over the examples.
- [x] Run it over every example and fuzzer corpus; any counterexample becomes a regression test.

## 3. Equality saturation (e-graphs) — size

**Status (2026-10-15): merged.** Hand-rolled e-graph with a never-worse guard; examples
unchanged, fuzz programs −0.2% typical. Follow-up: the compiler is nondeterministic on some
programs (seen on a level2 fuzz program) — worth a look.

The IR rewrites (ir.rs algebra, fuse patterns) are hand-ordered passes that can block each
other. An e-graph holds every equivalent form at once and extracts the cheapest by real
combinator cost.

- [x] Prototype with the `egg` crate on the scalar expression language: port the existing
      algebraic rewrites as rules; extraction cost = combinators (wire sums free, inlined
      conditions free, etc., mirroring `logic()`).
- [x] Compare against the current pipeline on all examples: must never be worse; find
      where it's better.
- [x] Range facts: rules guarded by facts (floor corrections, overflow) need a conditional
      rule mechanism or an analysis in the e-graph.
- [x] Decide what stays as dedicated passes (fuse patterns over bundles are probably too big
      for the e-graph at first).
- [x] Validate with item 2 on every rewrite rule.
- [x] Compile-time budget: node/iteration limits so big programs stay fast.

## 4. Superoptimisation — size

**Status (2026-10-15): merged.** Select picks: one decider for min/max/abs/ternaries with
runtime arms. Bench 2640 → 2621 (size 2589 → 2548), fuzz programs −10.4%. In-game probe of
OR'd each-terms with green copies pending.

Search offline for the fewest combinators computing small patterns, using the odd features
(multi-condition deciders, selector modes, `each`, wire sums). Results become rewrite rules.

- [x] Define the search space: 1–3 combinators of every kind and mode over up to 2–3 input
      signals and constants, with Factorio's exact semantics (reuse ticky-sim's evaluator).
- [x] Target patterns: harvest the most frequent small IR subgraphs from the examples and
      fuzz corpora (with their combinator cost today).
- [x] Search: enumerate + test on random vectors, confirm candidates with the solver (item 2).
- [x] Emit the winners as rules (into the e-graph from item 3, or as fuse patterns), with
      a generated table checked into the repo and the tool under `tools/`.

## 5. Operator sharing across process states — size

**Status (2026-10-14): measured, rejected.** 0 on examples, ~0.4% on fuzz corpora (every
shareable shape is a one-combinator op). See NOTES.md for when it would pay.

In a multi-cycle process, two expensive operations that never run in the same state could
share one set of combinators, inputs muxed by the program counter (high-level synthesis
"binding"). We share registers (liveness) but not logic.

- [ ] Find candidates: costly identical-shape operations (bundle ops, lookups, sorting
      networks, divisions with corrections) in different states of one process.
- [ ] Cost model: shared unit + input muxes + output demux vs. two units. Only for
      `--opt size`.
- [ ] Timing: the shared unit's latency must fit the states using it (or add a wait state,
      size mode only).
- [ ] Tests: processes where two branches do the same heavy work.

## 6. Profile-guided optimisation — speed

**Status (2026-10-14): merged.** Guides step merging/copying and speculation (not the
flattening budget, which is only a blow-up guard). primes loop 5 → 3 ticks/iteration.
In-game difftest of profiled builds pending.

The real analogue of branch prediction: run the program's tests in the simulator, record
which states and branches are hot, then flatten hot paths to fewer ticks and leave cold
ones compact.

- [x] Profile collection: `ticky test --profile out.json` counting per-state visits and
      per-branch outcomes in ticky-sim.
- [x] `build --profile out.json`: feed counts to the flattening budget and select-stage
      decisions (spend combinators where ticks are hot).
- [x] Without a profile, behaviour is unchanged.
- [x] Show the win: an example whose hot loop gets measurably fewer ticks per iteration.

## 7. Overlapping loop iterations (modulo scheduling) — speed

**Status (2026-10-15): merged.** Sound and fuzz-clean, but no example gets faster; the real
cases need bundle-typed pipeline registers, IR-level stages, or loop-test speculation
(follow-ups). With a profile, primes 3 → 2 ticks/iteration. In-game difftest pending.

A `while` loop in a process starts iteration i+1 while i finishes, when dependencies allow.

- [x] Dependency analysis on loop bodies: loop-carried dependences through state, memory
      (arrays/bundles) and waits; only loops without waits or I/O in the body at first.
- [ ] Initiation interval from the recurrence and resource bounds; emit a prologue, a
      steady-state kernel, and an epilogue in the step machine.
- [x] Exits mid-flight: iterations started speculatively past the exit must not commit.
- [x] `fuzz_procs.py` extended with loops of varying dependence distance.

## 8. Retiming — speed and size

**Status (2026-10-14): merged.** Little to win: −6 combinators (histogram, thruster); most
delays are forced by output alignment. In-game difftest pending (histogram, thruster).

Move delay combinators across logic so paths line up with fewer of them, cutting the holds
that keep pipelined blocks in step.

- [x] Measure first: count hold/delay combinators per example (combinator descriptions say
      what made them) to see whether there's enough to win.
- [x] Leiserson–Saxe retiming over the pipelined block's graph (`codegen/pipelined.rs`
      `at_ref` delays): minimise registers subject to the block's latency.
- [ ] Must keep tick-exact behaviour: difftest-critical.

## 9. Duplicating logic to save wire — layout

**Status (2026-10-14): merged.** Copies placed into the existing layout and re-routed
(re-annealing rejected: seed noise). Annealed: ~no effect. Grid: relays 201 → 111 behind
`--duplicate-drivers`; could become the default after an in-game difftest.

If a cheap combinator feeds two distant clusters, a copy next to each beats relay poles.

- [x] After placement, find networks needing relays whose driver is cheap (one combinator,
      inputs nearby both ends).
- [x] Duplicate, re-place (annealer), keep if relays + combinators drop.
- [x] Ties into today's layout objective (area, max width/height).

## 10. Signal packing — size

**Status (2026-10-15): surveyed, dropped.** Signal pressure is far from limits for real
programs; multi-condition/multi-output deciders already cover the savings; extracts cost
combinators and ticks. More bus networks would beat packing if capacity ever matters.

Range analysis knows when values are small; several booleans or small ints could share one
signal as bit fields, fewer signals on wires and sometimes fewer combinators.

- [x] Find what packing actually saves: signal pressure (wires running out of signals,
      bundles) vs. the extract cost (shift + mask = combinators).
- [x] Candidates: flag sets read together (masks tested at once by one decider), state
      registers.
- [x] Probably the most speculative item: drop it if the survey shows no win.

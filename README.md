# Ticky

A Python-like language that compiles to Factorio 2.0 combinator blueprints.
The full design is in [SPEC.md](SPEC.md); implementation notes and progress are in [NOTES.md](NOTES.md).

```python
input  charge: int @ A = port("Accumulator charge %")
output steam_on: bool @ S

every tick:
    if charge < 20:
        steam_on = True
    elif charge > 80:
        steam_on = False
```

**Status: levels 0–5.** Programs are made of ports, constants, `every` blocks and ordinary
sequential code (`while`, `for`, `if`, `break`/`continue`, `wait until`, `wait n`, `ticks()`),
with functions (`def`, defaults, keyword arguments, tuple returns), arrays (`[0] * 8`,
indexing, comprehensions, `sum`/`min`/`max`/`sorted`; arrays indexed at runtime live on
signals, SPEC §4.4), **bundles** (everything on a wire as one value, with element-wise
arithmetic, dict comprehensions and reductions, SPEC §4.3), concurrent **processes**
(`process name:`, SPEC §9.2), runtime checks (`--checks`, SPEC §13) and runtime **signals**
(`b.argmax()`, `Signal` ports and variables, `for s, v in b.items():`, SPEC §4.2, §4.3.4).

```python
input  stock: Bundle = port("Logistic network contents")
output request: Bundle = port("Requests")

WANT = Bundle(iron_plate=400, copper_plate=400, steel_plate=100, plastic_bar=200)

every tick:
    short = WANT - stock
    request = {s: v for s, v in short.items() if v > 0}
```

Modded signals work by exact name, with a type where an item and recipe share a name:
`S("nt-tbu-fuel")`, `S("nt-reprocess-hecf-249", type="recipe")`. Names Ticky doesn't know are
warnings, not errors.

```python
input  demand: Bundle             # each station's demand on its own virtual signal
input  train_waiting: bool @ T
output send_to: Signal            # the station with the largest demand, as that signal = 1

while True:
    wait until train_waiting
    send_to = demand.argmax()
    wait until not train_waiting
```

```python
input  start: bool @ S
input  n: int @ N
output result: int @ R

while True:
    wait until start
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b      # 2 ticks per iteration
    result = a
    wait until not start
```

## Usage

```bash
cargo build --release            # binary: target/release/ticky

ticky build prog.ticky -o prog.bp.txt   # blueprint string (+ cost report on stderr)
ticky build prog.ticky --json           # blueprint JSON instead
ticky build prog.ticky --opt=size       # fewest combinators (default: --opt=speed)
ticky build prog.ticky --no-poles       # no power poles (bring your own, e.g. substations)
ticky build prog.ticky --outputs=west   # output ports at the top left, each fed by its own pole line
ticky build prog.ticky --ports=ew --outputs=north   # all ports in one row along the north edge
ticky build prog.ticky --ports=ew       # inputs along the north edge, outputs along the south edge
ticky build prog.ticky --place=anneal   # experimental: smaller footprint by simulated annealing
ticky build prog.ticky --place=anneal --max-width 30   # ... at most 30 tiles wide (or --max-height)
ticky build prog.ticky --allow-unknown-signals         # no warnings for modded item/recipe names
ticky build prog.ticky --no-quality    # for games without the Quality mod (see below)
ticky build prog.ticky --checks        # runtime checks: error lamp + `error` code output
ticky check prog.ticky                  # errors, warnings and the cost report
ticky test  prog.ticky                  # run the program's `test` blocks in the simulator
ticky sim   prog.ticky --ticks 300 --set charge=10 --set charge=90@100   # print output changes
ticky difftest prog.ticky --ticks 300 --set ...   # simulator vs. real Factorio, tick by tick
ticky decode prog.bp.txt                # any blueprint string → JSON
```

`--set name=value@tick` changes an input at a tick (default tick 0); bundle inputs take
`--set stock=iron-plate:5,copper-plate:3@10`, and `Signal` inputs a signal name
(`--set want=coal`; `iron-plate@rare` for a quality). `RUN=0@tick` and `RUN=1@tick` switch the program
off and on.

## Using a compiled blueprint

- **Power:** the blueprint includes medium electric poles; connect one to your network. With
  `--no-poles` it has none and you power it yourself. Poles labelled "Ticky wire relay" carry
  long circuit wires and are always included.
- **RUN switch:** the constant combinator at the top left. It is saved **off**, so bots can finish
  building first. Turn it on to start the program; turning it off stops and resets it.
- **Inputs:** combinators down the left edge, under the RUN switch, in declaration order. Connect a
  red or green wire carrying the input's signal to the port's input (left) side. Each port only
  reads its own signal, so a busy factory wire is fine. A `Bundle` input reads everything on
  the wire; a `Signal` input reads which signal has the largest value on it (e.g. a constant
  combinator with one signal set). A `Signal` output sends its signal with value 1.
- **Outputs:** combinators down the right edge, in declaration order. With `--outputs=west`, the
  output ports sit at the west edge north of the blueprint, one row each (the first output
  northernmost), facing west; each is fed by its own line of poles (red wire) from a gate on the
  east edge. This costs one combinator and one tick per output; with `--place=anneal` the
  gates are placed with everything else and the lines become ordinary (relayed) wires. With
  `--ports=ew` the ports are in rows, first port westernmost: the RUN switch (above the error
  lamp) and the inputs along the north edge, wired from the north; outputs along the south
  edge, or with `--outputs=north` continuing the north row and wired from the north (no gates
  or pole lines). Wire from a port's output side to whatever should react. Hovering over a
  port shows its current value.
- **Quality:** by default the circuit carries its internal values on *quality* signals
  (uncommon to legendary), so it needs the Quality mod (part of Space Age), and every normal
  signal is yours: nothing a program reads or writes collides with the internals. Build with
  `--no-quality` for a game without it.
- **Error lamp** (`--checks` only): the lamp beside the RUN switch lights red when a runtime
  check fails (an `assert`, an index out of range, a division by zero); the `error` output
  (signal-E) gives the check's code, and the build report lists what each code means.
- **Screens** (`import display`, then `output s: display.Screen(W, H)`): a grid of lamps north
  of the rest (or `--display s=east`, …), with poles above and below it. Pixels are colours
  `0xRRGGBB` (0 = off); see SPEC §8.3 and `examples/screen.ticky`.
  Drawing: `rect`, `hline`, `vline`, `digit`, `number` and `text` (a 3×5 font), at
  positions known when compiling or computed; `examples/dashboard.ticky`.
- **Item data** (`import items`): `items.stack_size(b)`, `items.rocket_capacity(b)`, one
  selector combinator each (`--space-age` for Space Age's numbers); `examples/warehouse.ticky`.
- **Quality** (`import quality`): `quality.set(b, "rare")`, `quality.merge(b)`,
  `quality.of(sig)` and `if s.quality >= "rare"` in comprehensions; `examples/warehouse.ticky`.
- **Random numbers** (`import random`): `random.randint(lo, hi)`, `random.choice(b)`,
  `random.key(b)`, with `every=N`; `examples/dice.ticky`. Difftests skip values that depend on
  random picks.
- Every port's in-game description names it, e.g. *"Ticky output `half` (int): sends signal-H…"*.

## Layout of this directory

| Path | What |
|---|---|
| `crates/ticky-syntax` | Lexer, parser, AST, diagnostics |
| `crates/ticky-compiler` | Analysis, IR, lowering, codegen, layout, test runner |
| `crates/ticky-factorio` | Signals (dumped from the game), combinator integer semantics, blueprint encoding |
| `crates/ticky-sim` | Tick-exact simulator that runs the emitted entities and wires |
| `crates/ticky-cli` | The `ticky` binary |
| `examples/` | Example programs, each with tests; all are difftested against the game |
| `harness/` | Headless-Factorio harness used by `ticky difftest` (sandboxed in `/tmp/ticky-harness`); `difftest-examples.sh` runs every example |
| `tools/` | Fuzzers that check compiled circuits against Python itself |

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

**Status: levels 0–3.** Programs are made of ports, constants, `every` blocks and ordinary
sequential code (`while`, `for`, `if`, `break`/`continue`, `wait until`, `wait n`, `ticks()`),
with functions (`def`, defaults, keyword arguments, tuple returns), fixed-size arrays
(`[0] * 8`, indexing, comprehensions, `sum`/`min`/`max`) and **bundles**: everything on a wire
as one value, with element-wise arithmetic, dict comprehensions and reductions (SPEC §4.3).
Large RAM arrays and runtime `Signal` values come in later levels (SPEC §16).

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
ticky build prog.ticky --outputs=west   # also carry every output back west on its own pole line
ticky check prog.ticky                  # errors, warnings and the cost report
ticky test  prog.ticky                  # run the program's `test` blocks in the simulator
ticky sim   prog.ticky --ticks 300 --set charge=10 --set charge=90@100   # print output changes
ticky difftest prog.ticky --ticks 300 --set ...   # simulator vs. real Factorio, tick by tick
ticky decode prog.bp.txt                # any blueprint string → JSON
```

`--set name=value@tick` changes an input at a tick (default tick 0); bundle inputs take
`--set stock=iron-plate:5,copper-plate:3@10`. `RUN=0@tick` and `RUN=1@tick` switch the program
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
  the wire.
- **Outputs:** combinators down the right edge, in declaration order. With `--outputs=west`, each
  output also runs back on its own chain of medium poles (red wire) north of the blueprint, ending
  at a pole above the input column; the first output's line is the northernmost. Wire from a port's output
  (right) side to whatever should react. Hovering over a port shows its current value.
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

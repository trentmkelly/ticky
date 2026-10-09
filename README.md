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

**Status: levels 0–2.** Programs are made of ports, constants, `every` blocks and ordinary
sequential code (`while`, `for`, `if`, `break`/`continue`, `wait until`, `wait n`, `ticks()`),
with functions (`def`, defaults, keyword arguments, tuple returns) and fixed-size arrays
(`[0] * 8`, indexing, comprehensions, `sum`/`min`/`max`). Bundles and large RAM arrays come in
later levels (SPEC §16).

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
ticky check prog.ticky                  # errors, warnings and the cost report
ticky test  prog.ticky                  # run the program's `test` blocks in the simulator
ticky sim   prog.ticky --ticks 300 --set charge=10 --set charge=90@100   # print output changes
ticky difftest prog.ticky --ticks 300 --set ...   # simulator vs. real Factorio, tick by tick
ticky decode prog.bp.txt                # any blueprint string → JSON
```

`--set name=value@tick` changes an input at a tick (default tick 0). `RUN=0@tick` and `RUN=1@tick`
switch the program off and on.

## Using a compiled blueprint

- **Power:** the blueprint includes medium electric poles; connect one to your network.
- **RUN switch:** the constant combinator at the top left. It is saved **off**, so bots can finish
  building first. Turn it on to start the program; turning it off stops and resets it.
- **Inputs:** combinators down the left edge, under the RUN switch, in declaration order. Connect a
  red or green wire carrying the input's signal to the port's input (left) side. Each port only
  reads its own signal, so a busy factory wire is fine.
- **Outputs:** combinators down the right edge, in declaration order. Wire from a port's output
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

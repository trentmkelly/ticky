# Ticky — Language Specification (draft 0.2)

> A Python-like language that compiles to Factorio 2.0 combinator blueprints.

- **Status:** Levels 0–6 implemented (Level 3: the bundle core, §4.3.5; Level 4: signal
  arrays, §4.4; Level 5: processes and `--checks`, §9.2, §13; Level 6: runtime signals and
  bundle iteration, §4.2, §4.3.4), plus the first optimisation passes (see NOTES.md); later
  levels are design
- **Target:** Factorio 2.0. By default the compiler wires its internals with *quality*
  variants of signals (uncommon to legendary), which needs the Quality mod (part of Space
  Age); `--no-quality` builds for the base game alone, with normal signals inside.
- **Compiler:** Rust, single binary `ticky`
- **File extension:** `.ticky`
- **Name:** Ticky (decided 2026-10-08)

Items marked **[verify]** are assumptions about Factorio's behaviour that have to be confirmed
in-game (or against a `--dump-data` prototype dump) before the compiler relies on them.

**Verified in-game (2.0.77):** division and modulo by zero give 0; `/` truncates toward zero and
`%` takes the sign of the dividend; `MIN / -1 == 0`; `+ - * **` wrap; shift amounts are masked to
5 bits and `>>` is arithmetic; decider conditions group as OR-of-ANDs (AND binds tighter);
combinators, constant combinators and medium poles have a circuit wire reach of 9 tiles; 358
signals are usable in the base game (146 virtual, 204 item, 8 fluid).

**`each` semantics (verified with harness/ticky-harness/scenarios/probe):** an arithmetic `each`
operand iterates over the signals present on its selected networks; `each(red) op each(green)`
works over the **union** of both (missing = 0); a single output sums the per-signal results.
A decider with `each` in several conditions (mixed with ordinary conditions) iterates over the
signals of every `each` operand's networks, so a signal missing on one colour is tested as 0
there; outputting `each` copies or sets each passing signal, a single output sums over them
(constant 1 → a count). `everything`-output copies all signals of the chosen networks. The
selector combinator's `select` mode outputs the largest/smallest signal, `count` the number of
signals; with an index `k` it outputs the signal ranked `k` (nothing past the end); it reads the
sum of both wires.

**Quality (verified, Quality mod):** each quality of a signal is a separate signal everywhere:
`each`, `everything`, selectors, specific signals in conditions and outputs, constant
combinators. In blueprints a signal ID gets `"quality": "uncommon"` etc. So the compiler's
internal pool is the 358 base signals × 4 qualities = 1432 signals, and every normal-quality
signal is left to the program (ports, bundles).

---

## 1. Goals and non-goals

### Goals

1. **Code you can just write.** If it looks like Python and type-checks, it should compile and do
   what Python would do, with a short, explicit list of exceptions (§12).
2. **Custom hardware per program, not emulation.** The compiler builds circuitry specific to the
   program. A 5-line program gives a small blueprint.
3. **Fast enough to be practical.** Concrete performance targets (§11) that the compiler must
   meet and report against.
4. **Factorio-native data.** A wire can carry hundreds of signals at once. The `Bundle` type
   exposes that, and arrays are stored the same way, so many whole-collection operations cost a
   single tick.
5. **Trustworthy output.** A tick-accurate simulator matches the game exactly, and outputs never
   show half-updated (glitchy) values.

### Non-goals (v1)

- Python compatibility beyond the subset in this document. There are no classes, strings,
  floats, exceptions, imports of Python modules, generators or closures.
- Recursion. Functions are inlined; see §7.
- Floating-point maths. Fixed-point may come later.
- Running arbitrary existing Python code.

### Lessons from FAL

The Factorio Assembly Language project modelled Factorio as a sequential register machine with
no clock, then stalled on building memory cells and one-tick pulses. Ticky takes the opposite
approach. It accepts that Factorio is synchronous dataflow hardware, where every combinator is a
pipeline stage with 1 tick of latency, and makes timing, state and signal allocation the
compiler's job instead of the programmer's.

---

## 2. A first look

```python
# Count presses of a button and show the total on a lamp-based display.
input  button: int @ B
output total:  int @ T

total = 0
while True:
    wait until button > 0
    total += 1
    wait until button == 0
```

```python
# Smart requester: request whatever is below its target amount.
input  stock: Bundle
output request: Bundle

WANT = Bundle(iron_plate=400, copper_plate=400, steel_plate=100)

every tick:
    short = WANT - stock
    request = {s: v for s, v in short.items() if v > 0}
```

---

## 3. Program structure

A `.ticky` file is a module. It contains, in any order:

| Construct | Meaning |
|---|---|
| `input` / `output` declarations | The program's ports, i.e. where you wire it into your factory (§8). |
| Constant definitions | Module-level names assigned exactly once from a constant expression (§4.6). |
| State variables | Module-level names assigned more than once, or assigned at runtime. |
| `def` functions | Inlined at each call site (§7). |
| Top-level statements | The implicit `main` process (§9.1). |
| `process name:` blocks | Additional sequential processes that run concurrently (§9.2). |
| `every tick:` / `every N ticks:` blocks | Continuous logic (§10). |
| `test` blocks | Simulator-only tests, ignored by `ticky build` (§14.2). |

### 3.1 Lexical structure

- Python lexical rules: indentation-based blocks (4 spaces recommended; tabs are an error),
  `#` comments, newline-terminated statements, implicit line joining inside brackets, `\`
  continuation.
- Identifiers: `[A-Za-z_][A-Za-z0-9_]*`.
- Integer literals: decimal, `0x`, `0b`, `0o`, with `_` separators (`1_000_000`). They must fit
  in a signed 32-bit integer after constant folding, otherwise it is a compile error.
- `True` / `False` are the integers 1 / 0 (as in Python, `bool` is a subtype of `int`).
- String literals are allowed **only** as signal names (`b["iron-plate"]`), port labels and test
  names. There is no string type.
- Docstrings are allowed and ignored.

### 3.2 Keywords

Python keywords used with Python meaning: `if elif else while for in range break continue pass
def return and or not is True False global assert`.

Added keywords: `input output process every tick ticks wait until test`.
`tick` and `ticks` are only keywords inside `every …:` and `wait …` forms. `ticks()` is also a
builtin function (§9.4).

Reserved and rejected with a helpful error: `class lambda yield async await try except raise
with import from nonlocal del`.

---

## 4. Types and values

Every value has a static type. Types are inferred; Python-style annotations (`x: int = 0`) are
optional and checked.

| Type | What it is | Hardware representation |
|---|---|---|
| `int` | Signed 32-bit integer, wraps on overflow | One signal on a wire |
| `bool` | `int` restricted to 0/1 | One signal |
| `Signal` | Identifies a Factorio signal (`iron-plate`, `signal-A`…) | Compile time: nothing. Runtime: that signal with value 1. |
| `Bundle` | Map from `Signal` to `int`, where missing means 0 | All signals on a wire |
| `list[int, N]` | Fixed-size array of `N` ints | A bundle (§4.4) or RAM (§4.5) |
| `tuple` | Fixed group of values, for multiple assignment and returns only | Its parts, separately |

### 4.1 `int`

- Range −2³¹ … 2³¹−1. Arithmetic wraps (two's complement), as Factorio does.
- Uninitialised state does not exist: every variable must be assigned before use, which is
  checked statically. All state starts at its declared initial value when the program starts
  (§9.5).

### 4.2 `Signal`

- **Names.** Signal names are resolved in this order:
  1. An exact prototype name written with `_` in place of `-`: `iron_plate` → `iron-plate`.
  2. The same with a `signal-` prefix: `A` → `signal-A`, `red` → `signal-red`,
     `check` → `signal-check`.
  3. The string form is always exact: `S("iron-plate")`, `S("signal-A")`. A type picks among
     same-named signals (an item and its recipe): `S("iron-gear-wheel", type="recipe")`; types
     are `item` (the default), `fluid`, `virtual`, `recipe`, `quality`, `space-location` and
     `asteroid-chunk`.
  4. Names the compiler doesn't know (the base game, Space Age and all recipes are built in)
     are **warnings**, not errors, so modded signals work: `S("nt-tbu-fuel")`.
  5. Quality (Space Age): `S("iron-plate", quality="rare")` (`normal`, `uncommon`, `rare`,
     `epic`, `legendary`). Programs may use quality signals freely: they only ever share
     wires with the compiler's own (quality) signals on bundle wires, where the two are kept
     apart by wire colour.
- **Where signal names appear:** after `@` in port declarations, as `Bundle(...)` keyword
  arguments, in `bundle.name` attribute access, and through `S(...)`.
- **Signal-typed values** are compile-time constants, except values coming out of bundle
  iteration, `argmax`/`argmin`/`nth` (§4.3), `Signal` inputs, and variables assigned those.
  Runtime signals are carried as one-hot bundles, i.e. that signal with value 1; "no signal"
  (the `argmax` of an empty bundle) is the empty bundle. A variable holding signals has type
  `Signal` (inferred, or `x: Signal = …`); it may start as a constant (`last = S("coal")`).
- Comparison: `s == t`, `s != t` (two "no signal"s are equal). `s.value_in(b)` is the same as
  `b[s]`. `if s:` is true unless `s` is "no signal". Signals can't be used in arithmetic.
- With a runtime signal `s`: `b[s]` and `s in b` (1 combinator: `each × each`),
  `b.get(s, default)`, `b[s] = x` / `b[s] += x` (2 combinators), `{s: x, …}` (runtime keys
  are set one after another, so a repeated signal keeps its last value, as in Python), and
  choosing between signals (`s if c else S("coal")`).
- **Ports.** `input s: Signal` reads the signal with the largest value on its wires (ties as
  for `argmax`); `output t: Signal` sends the signal with value 1 (nothing for "no signal").
  Neither has `@`.

### 4.3 `Bundle`

A bundle is everything on one wire: up to several thousand distinct signals, each with an
`int` value. It behaves like Python's `collections.Counter`:

- A missing signal reads as 0. A signal with value 0 **is** missing; Factorio does not
  distinguish the two.
- Iteration order is defined by the operation (sorted views, §4.3.4). Otherwise it is
  unspecified.

#### 4.3.1 Construction

```python
WANT  = Bundle(iron_plate=400, copper_plate=400)   # keyword names → signals (§4.2)
EXACT = Bundle({"iron-plate": 400, "signal-A": 1})  # exact names
EMPTY = Bundle()
```

#### 4.3.2 Element-wise arithmetic

| Expression | Result | Notes |
|---|---|---|
| `a + b`, `a - b` | Per-signal sum/difference over the **union** of signals | A wire merge; nearly free |
| `a * b`, `a // b`, `a % b`, `a & b`, … | Per-signal over the signals present in **both** | Missing operand is 0 |
| `a * k`, `a // k`, `a + k`, … (`k` an `int`) | Applied to each **present** signal | `a + 5` does *not* create signals that were missing |
| `-a` | Per-signal negation | |

The "present signals only" rule for scalar operators is Factorio's `Each` semantics. It is the
main gotcha, so the compiler should warn on `bundle + nonzero_scalar` and `scalar - bundle`
(e.g. `500 - stock`), and suggest a target bundle such as `WANT - stock` as in §2.

#### 4.3.3 Filtering and mapping

Dict comprehensions over `.items()` produce bundles:

```python
low     = {s: v for s, v in stock.items() if v < 100}
doubled = {s: v * 2 for s, v in stock.items()}
flags   = {s: 1 for s, v in stock.items() if v > 0 and v < limit}
```

A comprehension compiles to element-wise hardware (1–3 ticks for the whole bundle, regardless of
size) when its key is `s`, and its value expression and condition use only `v`, scalars and
constants. Anything else, such as using `s` in arithmetic or calling functions with side effects,
is a compile error with an explanation. Sequential iteration is still available via `for` (§4.3.4).

#### 4.3.4 Reductions and queries

| Expression | Result | Cost target |
|---|---|---|
| `b[s]`, `b.iron_plate`, `b["iron-plate"]` | `int` | 1 tick (0 if `s` is constant and the value is already isolated) |
| `b.total()` | Sum of all values | 1 tick |
| `len(b)` | Number of present signals | 1 tick (selector: count) |
| `max(b.values())`, `min(b.values())` | `int` | 1–2 ticks (selector: sort) |
| `b.argmax()`, `b.argmin()` | `Signal` ("no signal" if `b` is empty) | 2 ticks |
| `b.nth(k)` | `(Signal, int)`, the k-th largest, 0-based (`k` may be a runtime value; out of range: no signal, 0) | 2 ticks |
| `s in b` | `bool`: is `b[s] != 0` | 1 tick |
| `for s, v in b.items():` | Sequential loop, descending by value | ~4 ticks/iteration |
| `for s, v in b.items(ascending=True):` | Sequential loop, ascending | same |
| `for s in b.keys():` | The same, without the values | same |

**Ties** (equal values) are ordered as the game's selector combinator orders them (verified
in-game with harness/ticky-harness/scenarios/tieprobe): items, then fluids, then virtual
signals (then recipes and the rest), each in prototype order, then by quality. `argmax` and
descending loops take that order; `argmin` and ascending loops the reverse. (For modded
signals the simulator's order is a best guess.)

Bundle iteration is sequential: it is a loop in a process (§9) and cannot appear in `every tick:`
blocks. It visits the signals present at loop entry (a snapshot); modifying `b` inside the loop
does not affect the iteration. Each iteration takes the top signal of the snapshot with a
selector combinator and removes it, so `break` and `continue` work as usual and the cost
doesn't depend on how many signals the bundle has.

#### 4.3.5 What level 3 implements

- `Bundle` ports (`input stock: Bundle`, no `@`), variables, constants and function
  parameters/results; bundle state in `every` blocks and the main program.
- Construction: `Bundle()`, `Bundle(name=value, …)` and dict literals, with runtime values
  (`Bundle(stone=-4000 if low else 0)`); `S(...)` signal constants (`FUEL = S("nt-fuel")`).
- Element writes: `b[sig] = x`, `b["name"] = x`, `b[sig] += x` (only that signal changes).
- Arithmetic: bundle `op` bundle (union), bundle `op` number and number `op` bundle (signals
  present only, with a warning for `+`/`-`), unary `-`, `==`/`!=` between bundles, `x if c else
  y`, truthiness (non-empty), augmented assignment.
- Reads: `b[sig]`, `b["name"]`, `b.name`, `b.get(sig, default)`, `sig in b`, `len(b)`,
  `b.total()`, `sum(b.values())`, `max(b.values())`, `min(b.values())` (0 for an empty bundle).
- Comprehensions `{s: value for s, v in b.items() if cond …}`: `value` and `cond` may use `v`,
  numbers, `+ - * // % & | ^`, comparisons, `and`/`or`/`not`, `x if c else y`, `min`, `max` and
  `abs`. The key must be `s`. Inside a comprehension (and between bundles) `//` and `%` truncate
  like Factorio (§12). Conditions on `v` itself cost one decider; conditions on other
  expressions of `v` (`v % 50 == 0`, `max(v - k, 0)`) compare a computed bundle with 0, with
  missing signals counted as 0.
- Level 6 adds `argmax`/`argmin`/`nth`, runtime `Signal` values and ports, `for s, v in
  b.items():` loops and quality signals (§4.2, §4.3.4).

### 4.4 `list[int, N]`

Fixed-size integer arrays. There is no `append`, `pop` or resizing in v1.

```python
xs = [0] * 16          # list[int, 16], all zeros
ys = [3, 1, 4, 1, 5]   # list[int, 5]
n  = len(xs)           # compile-time constant 16
```

| Operation | Meaning | Cost target |
|---|---|---|
| `xs[k]`, `k` constant | Read element (negative constants allowed, Python-style) | free / 1 tick |
| `xs[i]`, `i` runtime | Read element | ≤ 3 ticks |
| `xs[i] = v` | Write element | ≤ 3 ticks |
| `[f(x) for x in xs]` | Element-wise map, if `f` is element-wise pure | 1–3 ticks total |
| `[f(x, y) for x, y in zip(xs, ys)]` | Element-wise over two arrays | 1–3 ticks total |
| `sum(xs)`, `max(xs)`, `min(xs)` | Reductions | 1–2 ticks |
| `sorted(xs)`, `sorted(xs, reverse=True)` | New sorted array | 2 ticks, ~2N combinators |
| `for x in xs:` / `for i in range(len(xs)):` | Sequential loop | per §11 |
| `xs.index(v)` | First index with value `v`, or −1 | ≤ 3 ticks |
| `v in xs` | Membership | 1–2 ticks |

**Runtime index out of range:** reads return 0 and writes are dropped. With `--checks` the
program halts and lights its error lamp (§13). Negative *runtime* indices are out of range;
Python's wrap-around applies to constant indices only.

**Implemented (levels 2 and 4).** An array indexed only by constants is a *register array*:
every element is its own variable (`xs[3]` in messages), constant indexes are free, up to 256
elements. An array indexed at runtime anywhere (or longer than 256) is a *signal array*: a
bundle with element `k` on the `k`-th signal of the internal pool, split into banks of one pool
each (1431 elements with quality signals, 357 without), up to 4096 elements. The compiler finds
which arrays need it by expanding until the choice settles; arrays copied into a register array
are read out element by element. On signal arrays (verified in-game, harness probe `L*`):
- `xs[i]` (runtime): `I = i + 1` onto a private wire carrying the position table `T[k] = k+1`,
  then one decider `each(green) == I(green)` copying the array (red) onto one signal: 2 ticks,
  3 entities, any length. Constant indexes read one signal (1 combinator).
- `xs[i] = v`: a one-hot decider (positions red, index green) marks slot `i`; a decider keeps
  every other element; `onehot * v` writes the new one: 3 ticks. `xs[i] += d` needs no read
  (the array copied plus `onehot * d`).
- `[f(x) for x in xs]` (no filter, `f` without `//`, `%`, `**` or calls): one bundle
  comprehension per bank, plus `f(0)` on the slots holding 0 (zeros aren't on the wire).
- `sum` (total), `any`/`all` (signal counts), `min`/`max` (selector, corrected for zeros),
  `x in xs`, `xs.index(x)` (first matching position by selector), `xs.as_bundle()`.
- `sorted(xs)`, `sorted(xs, reverse=True)` (any array up to one bank): N selectors (rank `k`)
  on the keys `2x + 1` (never 0, so zeros sort too), each followed by `each >> 1 → T[k]`:
  2N + 1 combinators, 3 ticks. Values must be within ±2^30.
- Constant tables indexed at runtime (`[3, 1, 4, 1, 5][i]`) are one constant combinator and
  one read. Other unnamed arrays indexed at runtime still use a select.
Not yet: `zip`, `enumerate`, slices.

**Representation.** The compiler picks one per array:
- **Register array.** Every index is a compile-time constant, so each element is ordinary state.
- **Signal array.** Element `i` is stored on signal `T[i]`, taken from a fixed signal table
  generated from the prototype dump. Element-wise operations become `Each` combinators. Capacity
  is the size of the table, ~several hundred to a few thousand **[verify count]**.
- **Banked RAM.** Arrays larger than one signal table, or very write-heavy arrays, are split into
  banks of signal arrays.

The representation never changes program meaning, only cost.

### 4.5 Memory model

Each variable lives in exactly one place:
- **Temporaries** (values not live across a step boundary) are wires, with no storage.
- **State** (values live across a step or tick boundary) is a register: a combinator memory cell.
- **Arrays** are as in §4.4.

You never declare registers; the compiler decides.

### 4.6 Constants

A module-level name assigned exactly once, from an expression the compiler can fully evaluate,
is a constant. Constant expressions may call functions with constant arguments. Constants cost
no hardware unless used as a runtime value, in which case they become a constant combinator or a
combinator's literal operand. `ALL_CAPS` is conventional but not required.

---

## 5. Expressions and operators

Python precedence and associativity apply throughout.

| Operator | Semantics on `int` |
|---|---|
| `+ - *` | Wrapping 32-bit |
| `//`, `%` | **Python semantics**: floor division, and the result of `%` takes the sign of the divisor. Division by zero → 0 (see §12). |
| `/` | Compile error: "no floats; use `//`" |
| `**` | Integer power, wrapping. Negative exponent: `1/x**n` truncated, i.e. 0 unless the base is ±1 (Factorio behaviour, verified). |
| `<< >>` | Shifts. `>>` is arithmetic. The shift amount is masked to 5 bits (`x << 33 == x << 1`), as in Factorio (verified). |
| `& \| ^ ~` | Bitwise |
| `< <= > >= == !=` | Produce `bool`. Chaining (`0 <= x < 10`) works as in Python. |
| `and or not` | Boolean, short-circuiting (§5.2) |
| `x if c else y` | Conditional expression |
| `abs, min, max` (scalars), `clamp(x, lo, hi)` | Builtins |
| `tdiv(a, b)`, `tmod(a, b)` | Truncating division/modulo, i.e. Factorio's native behaviour. Faster when operands may be negative. |

### 5.1 Division cost note

Floor `//` and `%` cost the same as Factorio's native operators when the compiler can prove
the operands are non-negative, which covers most factory quantities. Otherwise they cost
1–2 extra ticks for sign correction, and `tdiv`/`tmod` are available if you want the native
behaviour.

### 5.2 Purity and short-circuiting

Expressions without calls, or with calls only to functions that contain no `wait` and no
writes to non-local state, are **pure**. The compiler may evaluate both sides of `and`, `or` and
`x if c else y` in parallel and select the result, which is usually faster. When an operand is
impure, short-circuiting is honoured with real control flow.

---

## 6. Statements

| Statement | Notes |
|---|---|
| `x = e`, `x: int = e`, `a, b = b, a + b` | Tuple assignment evaluates the whole right side first, as in Python |
| `x += e` (all arithmetic/bitwise ops) | |
| `xs[i] = e`, `xs[i] += e` | |
| `if / elif / else` | |
| `while cond:` | `while True:` is the normal way to write a program that runs forever |
| `for i in range(a, b, step):` | `step` must be a nonzero constant |
| `for x in xs:`, `for i, x in enumerate(xs):` | |
| `for s, v in b.items():` | §4.3.4 |
| `break`, `continue`, `pass`, `return` | |
| `wait until cond` | §9.3 |
| `wait n` | §9.3 |
| `assert cond` | Built with `--checks`: a failure halts the process, lights the error lamp and outputs a code (§13). Otherwise removed, like `python -O` (its expression isn't evaluated). |
| `print(...)` | Simulator only, logs with the tick number. Removed from blueprints (with a note in the build report). |
| `global x` | Required to assign module-level state inside a `def`, as in Python |

Assigning to an `input` is a compile error. Reading an `output` gives the value last written to it.

---

## 7. Functions

```python
def gcd(a, b):
    while b != 0:
        a, b = b, a % b
    return a
```

- Parameters are passed by value. Arrays and bundles are copied on write (`xs[i] = …` inside a
  function only modifies the caller's array if it is declared `global`). **This differs from
  Python**, where lists are shared references: return the changed array instead.
- Positional and keyword arguments; defaults must be constant. Multiple return values via
  tuples (`return a, b`; `x, y = f()`). Early `return`s anywhere, including inside loops.
- A function assigns module variables only if it declares them `global` (as in Python).
- Calls inside `and`, `or` and `x if c else y` only run when Python would run them.
- **How calls are compiled** (implemented):
  - Functions without loops or waits are **inlined** at each call. They usually become a few
    selects inside the caller's step, and cost nothing extra when their arguments are constant.
  - Functions with loops or waits, called from sequential code, are compiled **once as a
    subroutine**: arguments are assigned to its parameters, a return-address register records
    where to continue, and `return` jumps back through it. Calling one costs about a step.
  - In `every` blocks everything is inlined (their loops are unrolled).
  - The cost report lists each function, how it was compiled and how often it's called.
- Top-level code that only uses constants runs **at compile time**, including loops and
  function calls: `TABLE = [f(i) for i in range(16)]` costs no hardware.
- Recursion, direct or mutual, is a compile error in v1.
- Functions are not values: no passing functions around, no lambdas.

---

## 8. Ports: inputs and outputs

```python
input  power:  int    @ A        # scalar from signal-A
input  stock:  Bundle            # everything on the wire
input  target: Signal            # whichever signal is present (largest if several)
output lamp:   bool   @ L
output score:  int    @ S
output request: Bundle
output pick:   Signal            # emits that signal with value 1
```

Optional label: `input power: int @ A = port("Accumulator %")`, which becomes the combinator's
in-game description.

### 8.1 Physical layout

- Each `input` is a **port combinator** on the blueprint's left edge and each `output` one on
  the right edge, in declaration order, each with its label as the combinator description.
  Build options choose other arrangements (always in declaration order):
  - `--outputs=west`: outputs at the west edge too, north of the blueprint, each fed from a
    gate on the east edge by a line of poles (with `--place=anneal`, the gates are placed
    like any other combinator and wired to their ports directly, with relays as needed);
  - `--ports=ew`: ports in rows instead of columns, first port westernmost: the RUN switch
    (above the error lamp) and the inputs along the north edge (facing south), the outputs
    along the south edge (`--outputs=south`, default) or continuing the north row
    (`--outputs=north`, facing north). For wide, short blueprints.
- You connect a wire of **either colour** to an input port's input side, or to an output port's
  output side.
- Scalar inputs filter: an `int @ A` port only passes `signal-A`, so other signals on your
  factory wire cannot leak into the program. Bundle inputs pass everything.
- Outputs drive only their own port's output. Several outputs may share one port with
  `= port("Status", group="status")`, in which case their signals must be distinct.
- The compiler isolates bundles from its internal signals by wire colour and filtering, so a user
  bundle containing `signal-A` cannot collide with internal state that happens to use `signal-A`.

### 8.2 Sampling and glitch-freedom

- **Sampling.** Within one sequential step (§9.1), each input is sampled once. In `every tick:`
  blocks, all inputs are sampled on the same tick for a given block iteration.
- **Outputs are glitch-free.** An output only ever shows values that correspond to a consistent
  program state. Pipelines are latency-balanced so that no output ever briefly mixes new and old
  values. Several outputs written in the same step change on the same tick.

### 8.3 Screens (`import display`)

```python
import display

output screen: display.Screen(16, 6) = port("Level meter")

screen.fill(0x202020)                 # every pixel
screen[x, y] = 0xFF8800               # one pixel, x and y constant or computed
c = screen[3, 1]
```

- A screen is a grid of lamps, built into the blueprint beside the rest (`ticky build
  --display screen=north|south|east|west`, default north; several screens on one side sit side
  by side). Each lamp shows its pixel's low 24 bits as `0xRRGGBB` (the lamp's packed-RGB
  colour mode); a pixel of 0 is off.
- In code it is an array of `width × height` numbers, pixel `(x, y)` at index `y * width + x`
  (`screen[i]` also works), all 0 to begin with. It is a signal array (§4.4): a runtime write
  takes about 3 ticks; writes at constant positions in one step are combined into a few
  combinators, however many pixels (pixels set to the same value share them). `screen.width`
  and `screen.height` are constants. At most 4096 pixels.
- Like any variable, a screen has one writer (a process or `every` block); anything can read
  it. Tests read pixels with `screen[x, y]` (the value the lamp receives).
- **Power.** A row of medium poles runs just above and just below each screen, which powers
  screens up to 6 rows tall; taller screens need substations (the compiler warns), and with
  `--no-poles` powering everything is up to you.
- **Verified in-game** (scenario `rgbprobe`, difftests): the lamp shows `value & 0xFFFFFF`
  (so `-1` is white and `0x1000000` black), with "on while ≠ 0" as its condition; quality
  signals work as colour signals; the colour follows the network on the same tick, on/off one
  tick later.

### 8.4 Standard library peripherals

A fixed list of modules, each `import`ed like `display`. A peripheral is either hardware the
compiler builds into the blueprint (placed like screens, with a `--NAME=SIDE`-style option
where it has a position) or a function over bundles that maps to one combinator mode. None of
them adds new semantics to the core language: each lowers to existing IR plus at most one new
entity kind or combinator mode.

Every item is done when it has: the syntax below (or a documented improvement on it), the
entity behaviour checked in-game first with a harness probe scenario (findings in NOTES), the
simulator matching that probe, a test in `tests/examples.rs`, an example (or an addition to
one) that difftest-matches the game, and a line in the README.

- [ ] **1. `display` drawing.** On screens (§8.3), with positions and colours constant or
  computed:
  `screen.rect(x, y, w, h, c)`, `screen.hline(x, y, w, c)`, `screen.vline(x, y, h, c)`;
  `screen.digit(x, y, d, c)` (one 3×5 glyph, `d` 0–9); `screen.number(x, y, n, c, width=k)`
  (right-aligned decimal, `-` sign); `screen.text(x, y, "TEXT", c)` (constant string, built-in
  3×5 font of `A–Z 0–9` and `- . : ! ? % /` and space). Runtime rectangles should cost a few
  combinators however big (constant x/y tables plus masks), not one per pixel.
- [ ] **2. `display.Digits(n)`.** A numeric readout without a full screen:
  `output temp: display.Digits(4) = port("Temperature")`, assigned like an `int`
  (`temp = heat`), shown as `n` seven-segment digits of lamps (right-aligned, leading `-` for
  negatives, all segments of the top digit lit as an overflow mark). Placed like a screen.
- [ ] **3. `display.Panel`.** A display panel whose icon and message the program chooses:
  `output status: display.Panel({"ok": ("signal-check", "Running"), "low": ("signal-alert",
  "Low on fuel")}) = port("Status")`, then `status = "low"` (or a `Signal` for the icon alone).
  Each message is a panel condition on one internal value. The probe settles what shows when
  (map, alt-mode, hover) and documents it.
- [ ] **4. `speaker`.** A programmable speaker built in:
  `output siren: speaker.Alarm("Reactor too hot", icon="signal-fire") = port("Siren")`, `siren
  = heat > 900` (a global alert with that message and a sound while true), and
  `output tune: speaker.Notes(instrument="piano")`, `tune.play(note)` (note number, 0 = silent).
  The probe settles which instruments/notes and alert options exist in 2.0.
- [ ] **5. `controls`.** Player inputs inside the blueprint, so a program needs no wiring to
  be configured: `input go: controls.Switch("Start", on=False)` (a constant combinator the
  player toggles; `bool`) and `input target: controls.Setting("Target", 100)` (a constant
  combinator whose value the player edits; `int`). Placed with the ports.
- [ ] **6. `items`.** Game data from the selector combinator: `items.stack_size(b)` and
  `items.rocket_capacity(b)` (bundle → bundle, one combinator; fluids and virtual signals
  dropped; quality kept), and `items.stack_size(sig)` for a `Signal`. The simulator needs the
  stack sizes and rocket capacities dumped from the game (base, Space Age, quality mod).
- [ ] **7. `quality`.** Selector quality modes (needs the Quality mod; a compile error with
  `--no-quality`): `quality.set(b, "rare")` (everything re-tagged, values that coincide added;
  one combinator), `quality.set(b, sig)` (to the highest quality of `sig` on the input),
  `quality.merge(b)` (= `quality.set(b, "normal")`), and the filter
  `{s: v for s, v in b.items() if s.quality >= "rare"}` (any comparison against a constant
  quality; one combinator, combinable with conditions on `v`). Semantics as in NOTES
  2026-10-10 (scenario `qprobe`).
- [ ] **8. `random`.** The selector's random mode: `random.choice(b)` (a random present
  signal with its value, as a `Bundle` of one signal; `random.key(b)` for the `Signal`),
  `random.randint(lo, hi)` (constant bounds, at most one bank wide: a constant combinator of
  `lo..hi` plus a selector), with an optional `every=N` keyword for the update interval. The
  simulator uses a seeded generator; test assertions on random values should be ranges, and
  difftest compares everything except values derived from random picks (the program declares
  nothing; the compiler marks those outputs and the harness skips them).
- [ ] **9. Placement for every placed peripheral** (screens, digits, panels, speakers,
  controls). Either automatic, as screens are now (beside the logic on a chosen side), or a
  fixed offset the programmer picks: `output screen: display.Screen(16, 6) = port("Meter",
  at=(0, 10))`, `output temp: display.Digits(4) = port("Temp", at=(10, 20))`. The offset is in
  tiles from the top-left corner of the logic block (the combinators and ports, not counting
  peripherals; x east, y south; negative allowed) to the peripheral's own top-left corner.
  The logic grows east and south from that corner, so a peripheral keeps its place relative
  to it as the program changes.
  The CLI can override it (`--at NAME=X,Y`, beside `--display NAME=SIDE`). Fixed peripherals
  reserve their tiles (and their power poles), so placement, annealing and wire relays work
  around them. A peripheral any distance away is wired with a line of relay poles, as
  `--outputs=west` does (the build summary counts them); with `--place=anneal`, the
  combinators driving it are pulled towards it, so the line stays short. Overlapping
  peripherals are a compile error naming both. Peripherals without `at=` keep automatic
  placement.

---

## 9. Sequential code: processes

### 9.1 The `main` process

Top-level statements, in file order, form the `main` process. It starts when the program starts
(§9.5) and runs its statements once, like a Python script. If it reaches the end, it **halts**:
outputs keep their last values and `every tick:` blocks keep running. Write `while True:` for a
program that runs forever.

**The prologue.** The leading run of top-level assignments whose values are constant
expressions (each name at most once) runs "before time starts": a name assigned there and never
again is a constant; a name assigned there and again later (by `main` or by an `every` block)
starts with that value. So `total = 0` at the top of the file is an initial value, exactly as in
level 0, and `every` blocks see it from their first iteration.

**Variables** assigned by `main` are registers. Reading one before it is assigned on every path
is a compile error, unless it has a prologue value. `every` blocks may only read `main`'s
variables if they have a prologue value.

**Semantics.** The observable behaviour (outputs, and the order in which they change) is what
Python would produce if the statements ran instantaneously, except that time passes between
steps. The compiler groups statements into **steps**: sets of operations that can run in the same
clock period. Each step takes ≥ 2 ticks in the current compiler (one to settle, one to
commit). Simple `if`s inside straight-line code don't create steps (they become selects or
conditional loads); loops, waits and `if`s containing them do. Loops are rotated, so a simple
loop body is one step per iteration. The exact tick count of a step is not part of the
language. It is reported by the compiler and may improve between compiler versions. Programs that
need exact timing use `wait n`, `every N ticks:` or `ticks()`.

### 9.2 Additional processes

```python
process blinker:
    while True:
        light = not light
        wait 30
```

Each `process` is an independent state machine that runs concurrently with `main` and with the
other processes. Processes start together. A process that reaches the end of its body halts,
like `main`.

- **Variables.** A variable that a process assigns is the process's own, unless it has an
  initial value at the top of the file (the prologue, §9.1) or is a port: only those are
  shared, and subject to the single-writer rule (§9.6). So two processes (or a process and
  `main`) can each use `i`, `total`, … without clashing, while `ready = False` at the top
  makes `ready` one variable that one process writes and the others read. (Nothing else
  could be shared anyway: a variable without an initial value might not have been assigned
  yet when another process reads it.)
- **Functions** called from several processes are inlined per call or, when they contain
  loops or waits, compiled as one subroutine *per process* (each process has its own program
  counter, so it needs its own copy).
- Process names must differ from each other, from `main` and from function names.

### 9.3 Waiting

- `wait until cond` blocks until `cond` is true. If it is already true it takes no extra tick
  beyond the condition check (a wait step takes ≥ 2 ticks). `cond` is re-evaluated every tick,
  reading inputs and other processes' state fresh each time (everything else `main` reads is
  sampled once, when a step starts).
- `wait n` (`n` an `int`, runtime values allowed) pauses for exactly `n` ticks, counted from the
  start of the wait to the start of the next step, for `n ≥ 2` (a constant `n = 1` waits 2
  ticks; a runtime `n` waits at least as long as computing it takes). `wait 0` is a no-op;
  negative values act as 0.

### 9.4 Time

`ticks()` returns the number of ticks since the program started (wraps after ~414 days).
Hardware is only generated if it is used. Like an input, it is sampled when a step or block
iteration starts.

### 9.5 Starting, stopping, resetting

Bots build blueprints entity by entity, and a program that starts half-built would compute
garbage. So **every blueprint includes a RUN switch**: a constant combinator, saved as *off*,
next to the input ports. Blueprints built with `--checks` also include an error lamp (§13).

- While RUN is off, all state is held at initial values, all outputs read 0, and nothing runs.
- Turning RUN on starts everything on the same tick.
- Turning RUN off and on again is a full reset.
- `ticky build --autostart` leaves the switch out and starts as soon as the circuit is powered.
  Use it for pasting in the editor or sandbox.

Losing power freezes the circuit and losing combinators breaks it. Both are outside the language.

### 9.6 Sharing state between processes

- **Single writer.** Each state variable, array or output may be assigned by only one process or
  `every` block. A second writer is a compile error. Any process may read it.
- **Visibility.** A write committed on tick `t` is visible to every reader from tick `t + 1`.
  Writes within one process become visible in program order. So the usual "write the data, then
  set the flag; wait for the flag, then read the data" pattern is safe.
- For a value that several processes contribute to, give each its own variable and combine them
  in the reader.

**Implementation.** Each process is its own state machine (program counter, step timer and
commit pulse ANY). A reader samples other processes' variables when its own step starts (and
reads them live in `wait until`), so a write committed on tick `t` is seen by any step that
starts after `t`; writes in one step commit together. Verified in-game with §15.10
(examples/handshake.ticky) and fuzzed against Python with chains of processes that pass
results through "data, then flag" handshakes (tools/fuzz_procs.py).

---

## 10. Continuous code: `every` blocks

```python
every tick:
    if accumulator < 20:
        backup_on = True
    elif accumulator > 80:
        backup_on = False
```

### 10.1 Semantics

An `every` block behaves as if its body ran instantaneously, top to bottom with normal Python
meaning, once per **period**:

- Reads of state variables see the value at the start of the iteration, unless already assigned
  earlier in that same iteration.
- Locals that are assigned before they are read are temporaries (wires).
- Assignments to state and outputs take effect at the end of the iteration.
- Not allowed inside: `wait`, `while`, bundle iteration, `for` loops with non-constant bounds,
  and calls to functions that contain any of these. `for` loops over constant ranges or arrays are unrolled (with
  `break`/`continue`).

### 10.2 Period and latency

Hardware imposes two numbers on every block, and the compiler reports both:

- **Period `P`.** How often the body can run. It is limited by the longest *state recurrence*:
  if a state variable's next value depends on itself through `d` combinators, `P ≥ d`. Most
  blocks get `P = 1`. The compiler is expected to fuse common patterns; for example,
  `x = (x + 1) % N` and SR-latch logic like the example above each fit in a single decider
  combinator.
- **Latency `L`.** Ticks from an input changing to the corresponding outputs changing. Pure
  feed-forward blocks always have `P = 1` and some `L ≥ 1`.

`every tick:` means "every period, as fast as possible". When `P > 1`, the compiler **warns** and
names the recurrence responsible. `every N ticks:` (constant `N`) runs exactly every `N` ticks; it
is an error if `N < P`.

**Current implementation.** An `every tick:` block runs with `P = 1` as a pipeline when no state
feeds back into itself through a combinator: each state's next value is a constant, a copy,
conditional constants (latch logic, checked by the load deciders themselves), or an
accumulation `x += w` (optionally conditional, optionally with constant overrides such as a
reset) where `w` doesn't depend on the block's own state. Inputs then flow through continuously
and delay chains keep every combinator's operands on the same iteration. A pipelined block
starts committing `L` ticks after the program starts, so it only ever uses inputs read after
the start. Other blocks are multi-cycle with `P = depth + 1`; `x = (x + 1) % N` still needs
`P = 3` (planned: the single-decider form).

---

## 11. Performance contract

Unlike Python, Ticky has a performance specification. These are targets the compiler is measured
against with a benchmark suite (§14.3). They are not guesses for the user to verify.

| Construct | Target |
|---|---|
| Independent statements in one step | Run in parallel, no extra ticks |
| Simple statement (`x = a + b`) | ≤ 2 ticks (currently a step is ≥ 2 ticks) |
| Dependent chain of `k` operations within a step | ≈ `k` ticks (each combinator is 1 tick) |
| Loop iteration, small body | ≤ 4 ticks naive; 1–2 ticks when pipelined |
| `if`/`else` with pure branches | +0–1 tick (both branches computed, result selected) |
| `wait until c`, already true | ≤ 1 tick |
| Element-wise array/bundle op | 1–3 ticks total, any size |
| Array/bundle reduction (`sum`, `max`, `len`) | 1–2 ticks |
| Runtime array index read / write | ≤ 3 ticks |
| `every tick:` common patterns (counters, latches, filters) | `P = 1` |

### 11.1 What that means for programs

Sequential dependent work runs at roughly **10–60 steps per second** (60 ticks/s). Independent
work and bundle/array operations scale far better.

| Tier | Typical programs | Response time |
|---|---|---|
| Instant | Timers, latches, request maths, priority selection, min/max/sort of a bundle | < 0.1 s |
| Comfortable | Train dispatch over ~20 stations, small searches, displays, small number theory | 0.1–3 s |
| Sluggish | Element-by-element sorting of 100 numbers, primes to 1,000, a simple game loop | 3 s – 2 min |
| Impractical | Anything with ~100k+ dependent steps | Rewrite with bundles, or don't |

### 11.2 Optimisation modes

- `--opt=speed` (default) pipelines `every tick:` blocks wherever possible.
- `--opt=size` builds the program with and without pipelining and keeps whichever uses fewer
  combinators (pipelining sometimes saves combinators, since it needs no sample registers or
  clocks, and sometimes costs them, in delay chains).
- Planned: unrolling small loops and duplicating shared functions under `speed`.

### 11.3 Cost report

`ticky build` always prints a report. Example:

```
main            42 combinators   period  —   wait-free path: 7 ticks
  loop @ L12      3 ticks/iter  (recurrence: a,b at L13, 2 combinators)
process blinker  4 combinators
every tick @ L30  2 combinators  P=1 L=1
fn gcd (inlined ×1)  9 combinators   ~3 ticks/iter
total: 57 combinators, 6 poles, 14×9 tiles
```

---

## 12. Differences from Python

Each item is deliberate, and the compiler gives a specific error or warning where it can.

| Python | Ticky | Why |
|---|---|---|
| Unbounded ints | 32-bit wrapping | Factorio signals |
| `ZeroDivisionError` | `x // 0 == 0`, `x % 0 == 0`; `--checks` turns this into a halt + error lamp | Factorio behaviour; no exceptions |
| `/` gives a float | Compile error | No floats |
| `IndexError` | Read 0 / drop write; `--checks` halts | No exceptions |
| Lists grow | Fixed size | Hardware is fixed |
| Negative runtime indexes count from the end | Out of range (read 0, write dropped); constant negative indexes count from the end | One table lookup |
| `sorted` of any ints | Values within ±2^30 | Sort keys `2x + 1` must not wrap |
| Lists are shared references (`ys = xs` aliases) | Arrays are values: assignment and argument passing copy | Each array is its own set of registers |
| `list * 2` repeats | Same, but only with constants (`[0] * 16`); arrays have no element-wise operators, so use comprehensions | Avoids ambiguity with bundles |
| Dicts | Only `Bundle`, signal → int | Wire semantics |
| `Counter + Counter` drops counts ≤ 0 | Bundle `+`/`-` keep every nonzero result (negative too) | Per-signal wire sums |
| `//`, `%` floor | On bundles and inside bundle comprehensions they truncate (Factorio's rule); on numbers they floor as in Python | One combinator for the whole bundle |
| `b + 5` (if it existed) | Changes only the signals `b` has (Factorio's `each`); warns | Wire semantics |
| Iterating a dict follows insertion order | `for s, v in b.items()` goes from the largest value down (ties in the game's signal order) | Wire values have no insertion order; the selector combinator sorts |
| `max(d, key=d.get)` of an empty dict raises | `b.argmax()` of an empty bundle is "no signal" | No exceptions |
| Recursion | Compile error | No call stack (yet) |
| `print` | Simulator only | No console in-game |
| Strings, floats, classes, exceptions, imports | Absent | v1 scope |

---

## 13. Runtime checks and the error lamp

`ticky build --checks` adds runtime checks. The blueprint then has an **error lamp** next to
the RUN switch and an extra output port, `error` (signal-E; the name is reserved under
`--checks`):

- `assert` failures, out-of-range runtime indexes (reads and writes, negative indexes
  included) and division or remainder by zero (`//`, `%`, `//=`, `%=`; not `tdiv`/`tmod`,
  which are Factorio's operations by name) are checked.
- A check only fails where Python would actually evaluate it: `x // y if y else 0`,
  `y != 0 and x // y > 3` and divisions inside `if y:` never fail when `y` is 0.
- When a check fails in a process (`main` or a `process`), that step doesn't commit: the
  process halts there, the lamp lights (red) and `error` gives the check's **code**. The build
  report lists every code with its line, column, kind and process. Other processes keep
  running. The first failure's code stays until the program is reset (RUN off and on).
- In an `every` block a failed check lights the lamp and records the code, and the block keeps
  running (it has no single place to stop). Blocks with checks run multi-cycle rather than
  pipelined, so `--checks` can make such a block slower.
- If checks in two processes fail on the very same tick, their codes add up.
- Asserts whose value is known when compiling are checked then. A step with checks may take a
  tick longer, because the checks must be ready one tick before the step commits.

Without `--checks` there is no lamp and no `error` port: asserts are removed, and division by
zero and out-of-range indexes behave as in §12.

---

## 14. Tooling

### 14.1 CLI

```
ticky build prog.tick [-o out.txt] [--opt=…] [--checks] [--autostart] [--poles=medium|substation]
ticky sim   prog.tick --ticks 600 [--set button=1@100] [--trace total,lamp] [--vcd out.vcd]
ticky test  prog.tick            # runs test blocks
ticky check prog.tick            # parse + typecheck + report, no output
ticky fmt   prog.tick
```

`build` writes the standard blueprint string (`0` + base64(zlib(JSON))). With
`--json` it writes the raw JSON. The blueprint gets a name, a description listing its ports, and
icons.

### 14.2 Tests

```python
test "fibonacci":
    set start = 1
    run until result != 0, max 10_000 ticks
    assert result == 6765

test "latch holds":
    set accumulator = 10
    run 5 ticks
    assert backup_on
    set accumulator = 50
    run 5 ticks
    assert backup_on          # hysteresis: still on
```

Test-only statements: `set port = value`, `run N ticks`, `run until cond, max N ticks`. Tests run
in the simulator with RUN switched on at tick 0.

### 14.3 Correctness and performance verification

- **Simulator.** Models combinators tick-exactly as Factorio 2.0 does: wire summing, `Each`/
  `Anything`/`Everything` semantics, decider multi-condition rules, selector modes, and integer
  edge cases.
- **Differential testing.** A headless Factorio harness, building on the existing in-game test
  scripts in this repo, pastes compiled blueprints, runs N ticks and reads the ports from Lua.
  Results must match the simulator bit-for-bit. Every **[verify]** item in this spec becomes a
  test here.
- **Benchmarks.** The example programs below, with their §11 targets, form the benchmark suite.
  Regressions fail CI.

---

## 15. Example programs

Tier estimates are design targets.

### 15.1 Blinker (instant, `every`)

```python
output lamp: bool @ L

every 30 ticks:
    lamp = not lamp
```

### 15.2 Backup power with hysteresis (instant, `every`)

```python
input  charge: int @ A      # accumulator %
output steam_on: bool @ S

every tick:
    if charge < 20:
        steam_on = True
    elif charge > 80:
        steam_on = False
```
Expected: 1 decider combinator, `P = 1`, `L = 1`.

### 15.3 Smart requester (instant, bundles)

```python
input  stock: Bundle
output request: Bundle

WANT = Bundle(iron_plate=400, copper_plate=400, steel_plate=100, plastic_bar=200)

every tick:
    short = WANT - stock
    request = {s: v for s, v in short.items() if v > 0}
```
Expected: ~3 combinators, `L ≈ 2`.

### 15.4 Throughput meter (instant, state + `every`)

```python
input  belt_count: int @ I      # pulse-mode belt read
output per_minute: int @ M

window = [0] * 60
total = 0
i = 0

every tick:
    total += belt_count - window[i]
    window[i] = belt_count
    i = (i + 1) % 60
    per_minute = total * 60
```
Expected: fails `P = 1` (array read-modify-write recurrence) and is warned. The suggested fix is
`every 3 ticks:` or a pure-`every` delay-line rewrite. This example deliberately exercises the
period diagnostics.

### 15.5 Fibonacci (comfortable, sequential)

```python
input  start: int @ S
input  n: int @ N
output result: int @ R

def fib(n):
    a, b = 0, 1
    for _ in range(n):
        a, b = b, a + b
    return a

while True:
    wait until start > 0
    result = fib(n)
    wait until start == 0
```
Expected: ~2 ticks/iteration; `fib(20)` in under a second.

### 15.6 Collatz steps (comfortable, sequential with branches)

```python
input  x: int @ X
output steps: int @ S

def collatz(n):
    count = 0
    while n != 1:
        n = n // 2 if n % 2 == 0 else 3 * n + 1
        count += 1
    return count

last = 0
while True:
    wait until x != last and x > 0
    last = x
    steps = collatz(x)
```
Exercises: pure conditional expression → parallel branches; non-negativity proof for `//`/`%`.

### 15.7 Train dispatcher (comfortable, bundles + signals)

```python
input  demand: Bundle             # each station's demand on its own virtual signal
input  train_waiting: bool @ T
output send_to: Signal

while True:
    wait until train_waiting
    send_to = demand.argmax()
    wait until not train_waiting
```
Expected: ~3 ticks per dispatch regardless of the number of stations. Implemented as
examples/dispatch.ticky: 3 ticks per dispatch, 15 combinators.

### 15.8 Prime counter (sluggish, nested loops)

```python
input  limit: int @ N
output count: int @ C

def is_prime(n):
    if n < 2:
        return False
    d = 2
    while d * d <= n:
        if n % d == 0:
            return False
        d += 1
    return True

c = 0
for k in range(limit + 1):
    if is_prime(k):
        c += 1
count = c
```
Expected: `limit = 1000` in ~10–60 s. The point is to measure loop overhead.

### 15.9 Sorting: the slow way and the fast way

```python
output slow_done: bool @ D
output fast_max: int @ M

xs = [(k * 7919) % 101 for k in range(32)]   # constant: folded at compile time

# Bubble sort, sluggish: ~500 compare-swaps
ys = xs
for i in range(len(ys)):
    for j in range(len(ys) - 1 - i):
        if ys[j] > ys[j + 1]:
            ys[j], ys[j + 1] = ys[j + 1], ys[j]
slow_done = True

# Built-in, instant
zs = sorted(xs)
fast_max = zs[-1]
```
Shows the gap between sequential code and Factorio-native operations.

### 15.10 Two processes and a handshake (comfortable, concurrency)

```python
input  ore: int @ O
output alarm: bool @ A
output report: int @ R

low_ticks = 0           # written only by `watch`
ready = False           # written only by `watch`

process watch:
    while True:
        if ore < 1000:
            low_ticks += 1
        if low_ticks >= 600:
            ready = True
            wait until ready_ack
            ready = False
            low_ticks = 0
        wait 1

ready_ack = False       # written only by main
while True:
    wait until ready
    alarm = True
    report = low_ticks
    ready_ack = True
    wait until not ready
    ready_ack = False
    wait 300
    alarm = False
```
Exercises: the single-writer rule and visibility ordering (§9.6). Implemented as
examples/handshake.ticky (with 60 and 30 instead of 600 and 300, so its tests run quickly);
`watch` takes 5 ticks per iteration, so the alarm sounds after 60 iterations, not ticks.

### 15.11 Higher / lower guessing game (comfortable, interactive)

```python
input  guess:  int @ G           # player sets a constant combinator
input  submit: bool @ S
output higher: bool @ H
output lower:  bool @ L
output win:    bool @ W

secret = (ticks() * 7919) % 100 + 1     # "random" enough

while True:
    wait until submit
    higher = guess < secret
    lower  = guess > secret
    win    = guess == secret
    wait until not submit
```

### 15.12 Histogram (comfortable, runtime-indexed array)

```python
input  sample: int @ V     # values 0..63
input  strobe: bool @ S
output bins: Bundle

hist = [0] * 64

while True:
    wait until strobe
    hist[clamp(sample, 0, 63)] += 1
    bins = hist.as_bundle()      # element i on SIGNAL_TABLE[i]
    wait until not strobe
```
Exercises signal-array RAM with a runtime index. **Open:** whether `as_bundle()` belongs in v1
(see §17).

---

## 16. Implementation architecture (non-normative)

Rust workspace:

| Crate | Responsibility |
|---|---|
| `ticky-syntax` | Lexer (indentation-aware), parser → AST, spans for diagnostics |
| `ticky-sema` | Name resolution, signal resolution against prototype data, type inference, purity, single-writer check, inlining |
| `ticky-ir` | Two levels: **CFG IR** (processes as control-flow graphs of steps) and **dataflow IR** (word-level operation graph with explicit registers) |
| `ticky-sched` | Turns CFGs into state machines: packs operations into steps (list scheduling), chains combinational logic, pipelines loops, shares resources |
| `ticky-opt` | Constant folding, CSE, fusion into multi-condition deciders and `Each` ops, dead-signal removal, range analysis (for floor-division elision) |
| `ticky-timing` | Retiming and latency balancing, period/latency computation for `every` blocks |
| `ticky-alloc` | Signal and wire-colour allocation (interference graph colouring), bundle isolation |
| `ticky-layout` | Placement (simulated annealing), wire routing within reach, pole/substation insertion, port placement |
| `ticky-blueprint` | Factorio 2.0 blueprint JSON → zlib → base64 |
| `ticky-sim` | Tick-exact combinator simulator operating on the *emitted entity graph*, not the IR, so it tests what actually ships |
| `ticky-cli` | The `ticky` binary |
| `data/` | Signal tables and prototype facts (wire reach, etc.) generated from `factorio --dump-data` |

Pipeline:

```
source ─parse→ AST ─sema→ typed AST ─lower→ CFG IR ─sched→ FSM + dataflow IR
       ─opt→ ─timing→ ─alloc→ entity graph ─layout→ placed entities ─encode→ blueprint
                                         └──────────── sim ────────────┘
```

### Suggested build order

1. ✅ **Level 0:** `every tick:` with scalar `int`/`bool`, ports, simulator, blueprint output with a
   naive grid layout. The first in-game result.
2. ✅ **Level 1:** sequential `main`: `if`/`while`/`for range`/`wait`, state machine synthesis, RUN
   switch. (Tuples in assignments and the cost report also exist already.)
3. ✅ **Level 2:** functions (inlining and subroutines), tuples, register arrays (constant and
   small runtime indexes), comprehensions, compile-time execution of setup code.
4. ✅ **Level 3:** `Bundle`: element-wise operations, comprehensions, reductions, selector
   combinator queries (§4.3.5; `argmax`/`nth` move to level 6).
5. ✅ **Level 4:** signal arrays and banked RAM, runtime indexing, `sorted` (§4.4).
6. ✅ **Level 5:** `process` concurrency, single-writer rule, `--checks`.
7. ✅ **Level 6:** bundle iteration, runtime `Signal` values (and `argmax`/`argmin`/`nth`,
   `Signal` ports, quality signals).
8. **Optimisation passes:** ✅ decider fusion, guarded loads, loop rotation, one-tick
   pipelining and accumulators for `every tick:`, `--opt` modes, signal namespaces per logic
   cluster. Still to do: loop pipelining in `main`, one-tick steps, single-decider counters,
   general retiming, real placement.
9. **Standard library peripherals** (§8.4): ✅ lamp screens; the rest is the checklist there.
10. **Later:** recursion via a RAM stack, fixed-point numbers, and possibly option A (a general
   CPU backend) as a separate target.

Each level ends with its examples from §15 passing in the simulator **and** in the headless-
Factorio differential harness.

---

## 17. Open questions

1. ~~**Name.**~~ Decided: Ticky.
2. **Array ↔ bundle conversion.** Should `xs.as_bundle()` / `Bundle → list` be exposed, given
   that it leaks the internal signal table? Alternative: arrays declared with explicit signals,
   e.g. `list[int] @ [A, B, C, …]`.
3. ~~**Displays.**~~ Lamp screens: §8.3. Display panels only show a fixed label on hover, so
   they're low priority. Drawing helpers, digits and panels are on the §8.4 checklist.
4. **Floor division default.** This spec picks Python semantics for `//` and `%`. If negative
   numbers turn out to be common in real programs, reconsider making truncation the default.
5. **`every tick` naming.** Since `P` can be > 1, should the as-fast-as-possible form be named
   something else (`always:`), reserving `every tick:` for a hard `P = 1` guarantee?
6. **Space Age.** Quality-variant signals greatly enlarge the signal table, and therefore array
   capacity. Should arrays use them automatically when Space Age is detected, or only on request?
7. **Multiple blueprints.** Should a program be able to target multiple physical blocks connected
   by long-distance wires, or radar in Space Age?

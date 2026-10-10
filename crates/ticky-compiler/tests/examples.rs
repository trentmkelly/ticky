//! Compiles every example program, checks its layout and runs its `test` blocks.

use std::path::Path;

use ticky_compiler::testrun::run_tests;
use ticky_compiler::{compile, Options};

fn opts() -> Options {
    Options { label: "test".into(), ..Default::default() }
}

#[test]
fn examples_compile_and_pass() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut count = 0;
    for entry in std::fs::read_dir(&dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_none_or(|e| e != "ticky") {
            continue;
        }
        count += 1;
        let src = std::fs::read_to_string(&path).unwrap();
        let name = path.display().to_string();
        // `# ticky: --checks` on the first line: the tests need runtime checks.
        let checks = src.starts_with("# ticky: --checks");
        let opts = || Options { checks, ..opts() };
        let c = compile(&src, &opts()).unwrap_or_else(|d| {
            panic!("{}", d.iter().map(|d| d.render(&name, &src)).collect::<String>())
        });
        assert!(c.cg.netlist.validate(true).is_empty());
        // The placement options give valid layouts too.
        // (Programs using `import quality` need quality signals.)
        let other = Options { poles: false, outputs_west: true, quality: src.contains("import quality"), ..opts() };
        let c2 = compile(&src, &other).unwrap_or_else(|d| panic!("{name} (no poles, west outputs): {}", d[0].message));
        assert!(c2.cg.netlist.validate(false).is_empty());
        assert_eq!(c2.layout.poles, 0);
        // So does the experimental annealing placement, deterministically.
        let a = ticky_compiler::place::AnnealOpts { effort: 0.2, ..Default::default() };
        let annealed = Options { anneal: Some(a), ..opts() };
        let c3 = compile(&src, &annealed).unwrap_or_else(|d| panic!("{name} (annealed): {}", d[0].message));
        assert!(c3.cg.netlist.validate(true).is_empty(), "{name} (annealed)");
        assert_eq!(compile(&src, &annealed).unwrap().blueprint_string(), c3.blueprint_string(), "{name}: annealing isn't deterministic");
        // Ports in rows (E-W), outputs south or north; annealed gates with west outputs.
        for (ports_ew, outputs_west, anneal) in [(true, false, None), (true, true, None), (true, true, Some(a)), (false, true, Some(a))] {
            let o = Options { ports_ew, outputs_west, anneal, ..opts() };
            let c4 = compile(&src, &o).unwrap_or_else(|d| panic!("{name} (ew {ports_ew}, west {outputs_west}): {}", d[0].message));
            assert!(c4.cg.netlist.validate(true).is_empty(), "{name} (ew {ports_ew}, west {outputs_west})");
        }
        for r in run_tests(&c, &src) {
            if let Some(d) = r.failure {
                panic!("{name}: test {} failed:\n{}", r.name, d.render(&name, &src));
            }
        }
        // The blueprint string decodes back to the same JSON.
        let json = c.blueprint_json();
        assert_eq!(ticky_factorio::blueprint::decode(&c.blueprint_string()).unwrap(), json);
    }
    assert!(count >= 5);
}

fn error_of(src: &str) -> String {
    match compile(src, &opts()) {
        Ok(_) => panic!("expected an error for:\n{src}"),
        Err(d) => d.iter().map(|d| d.message.clone()).collect::<Vec<_>>().join("\n"),
    }
}

#[test]
fn helpful_errors() {
    assert!(error_of("input x: int @ X\nevery tick:\n    x = 1\n").contains("inputs can't be assigned"));
    assert!(error_of("output y: int\nevery tick:\n    y = 1\nevery tick:\n    y = 2\n").contains("more than one"));
    assert!(error_of("output y: int\nevery tick:\n    y = z\n").contains("`z` is not defined"));
    assert!(error_of("output y: bool\nevery tick:\n    y = 5\n").contains("bool"));
    assert!(error_of("input c: int\noutput y: int\nevery tick:\n    if c:\n        t = 1\n    y = t\n").contains("might not be assigned"));
    assert!(error_of("output y: int\nevery tick:\n    y = 7 / 2\n").contains("no floats"));
    assert!(error_of("output y: int\nevery 1 ticks:\n    y = (y + 1) % 7 * 3\n").contains("at least"));
    // Modded signals by exact name and type: warnings only, and the right signal type.
    let c = compile("output o: Bundle\nevery tick:\n    o = {S(\"nt-tbu-fuel\"): 1, S(\"nt-reprocess-x\", type=\"recipe\"): 2}\n", &opts()).unwrap();
    assert_eq!(c.warnings.len(), 2);
    let json = c.blueprint_json().to_string();
    assert!(json.contains(r#"{"name":"nt-tbu-fuel","index"#) && json.contains(r#"{"type":"recipe","name":"nt-reprocess-x","index"#), "{json}");
    // Unknown signals (e.g. from mods) are warnings, not errors.
    let c = compile("output y: int @ nonsense_signal\n", &opts()).unwrap();
    assert!(c.warnings.iter().any(|w| w.message.contains("unknown signal")));
    assert!(error_of("output y: int\ndef f(n):\n    return f(n - 1)\ny = f(3)\n").contains("recursion"));
    assert!(error_of("output y: int\ndef f(a, b):\n    return a\ny = f(1)\n").contains("needs an argument for `b`"));
    assert!(error_of("output y: int\ndef f():\n    pass\ny = f()\n").contains("doesn't return a value"));
    assert!(error_of("output y: int\nxs = [1, 2, 3]\ny = xs[5]\n").contains("out of range"));
    assert!(error_of("output y: int\nxs = [1, 2, 3]\ny = xs\n").contains("array of 3"));
    assert!(error_of("input n: int\noutput y: int\nevery tick:\n    for i in range(n):\n        y += i\n").contains("constant"));
    assert!(error_of("output y: int\nxs = [0] * 3\nxs = [0] * 4\n").contains("an array of 4"));
    assert!(error_of("output y: int\nwhile True:\n    y = z + 1\n    z = 1\n").contains("before it's assigned"));
    assert!(error_of("output y: int\nevery tick:\n    y = z\nwait 5\nz = 1\n").contains("might not have run yet"));
    assert!(error_of("output y: int\nevery tick:\n    y = 1\nwait 1\ny = 2\n").contains("more than one"));
    assert!(error_of("break\n").contains("outside a loop"));
    // Bundles.
    let b = "input b: Bundle\noutput o: Bundle\noutput y: int\n";
    assert!(error_of(&format!("{b}every tick:\n    y = b\n")).contains("is a number, but this value is a bundle"));
    assert!(error_of(&format!("{b}every tick:\n    y = b < 5\n")).contains("only be compared with `==`"));
    assert!(error_of(&format!("{b}every tick:\n    o = {{s: v for s, v in b.items() if s > 3}}\n")).contains("can only be used as the key"));
    assert!(error_of(&format!("{b}def f(x):\n    return x\nevery tick:\n    o = {{s: f(v) for s, v in b.items()}}\n")).contains("can't be called inside"));
    assert!(error_of("input b: Bundle @ A\n").contains("no `@ signal`"));
    assert!(error_of(&format!("{b}every tick:\n    o = b + 1 if y else 0\n")).contains("the other side is a bundle"));
    assert!(error_of("for i in range(0, 10, 0):\n    pass\n").contains("can't be 0"));
    // Processes.
    assert!(error_of("output y: int\nprocess a:\n    y = 1\nprocess b:\n    y = 2\n").contains("more than one process"));
    assert!(error_of("output y: int\nprocess a:\n    x = 1\nprocess b:\n    y = x\n").contains("belongs to process `a`"));
    assert!(error_of("output y: int\nprocess a:\n    y = 1\nprocess a:\n    y = 2\n").contains("already the name"));
    assert!(error_of("output y: int\ninput k: int\nx = k\nprocess a:\n    y = x\n").contains("might not have run yet"));
    assert!(error_of("output y: int\nwhile True:\n    process a:\n        y = 1\n").contains("top level"));
    // Runtime signals.
    let sg = "input b: Bundle\noutput o: int @ O\noutput t: Signal\n";
    assert!(error_of(&format!("{sg}every tick:\n    o = b.argmax() + 1\n")).contains("signals can't be used in arithmetic"));
    assert!(error_of(&format!("{sg}every tick:\n    o = b.argmax() < b.argmin()\n")).contains("only be compared with `==` and `!=`"));
    assert!(error_of(&format!("{sg}every tick:\n    o = b.argmax()\n")).contains("is a number, but this value is a signal"));
    assert!(error_of(&format!("{sg}every tick:\n    t = 5\n")).contains("is a signal, but this value isn't"));
    assert!(error_of(&format!("{sg}every tick:\n    for s, v in b.items():\n        o += v\n")).contains("can't be used in an `every` block"));
    assert!(error_of(&format!("{sg}every tick:\n    o = b.nth(0)\n")).contains("tuple"));
    assert!(error_of(&format!("{sg}while True:\n    for s in b.items():\n        o += 1\n")).contains("two names"));
    assert!(error_of("input s: Signal @ A\n").contains("no `@ signal`"));
    assert!(error_of("output o: Bundle\no = {S(\"coal\", quality=\"shiny\"): 1}\n").contains("unknown quality"));
    // `--checks` reserves the `error` port.
    let c = compile("output error: int\nerror = 1\n", &Options { checks: true, ..opts() });
    assert!(c.is_err_and(|d| d[0].message.contains("reserved")));
}

/// Variables a process assigns are its own unless they have an initial value at the top of
/// the file; subroutines are compiled once per process.
#[test]
fn processes_have_their_own_variables() {
    let src = "output a: int @ A\noutput b: int @ B\ndef tri(k):\n    t = 0\n    for i in range(k + 1):\n        t += i\n    return t\n\
               process p:\n    for i in range(3):\n        wait 2\n    a = tri(4) + 2\n\
               for i in range(5):\n    wait 1\nb = tri(3) + 4\n\
               test \"t\":\n    run 100 ticks\n    assert a == 12 and b == 10\n";
    let c = compile(src, &opts()).unwrap();
    assert_eq!(c.cg.procs.len(), 2);
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "{:?}", r.failure.map(|d| d.render("t", src)));
    }
}

#[test]
fn constants_fold_away() {
    let src = "K = 6 * 7\nW = K // 4 - -3 % 2\noutput y: int @ Y\nevery tick:\n    y = W + 0\n";
    let c = compile(src, &opts()).unwrap();
    assert_eq!(c.program.consts["W"], ticky_compiler::ir::Cv::Int(9));
    // y = 9 is loaded with a constant: no arithmetic combinators in the block.
    assert_eq!(c.cg.blocks[0].depth, 0);
}

/// Ports keep their declaration order on the blueprint in every layout mode: inputs top to
/// bottom on the west edge, outputs top to bottom (east edge, or rows north with
/// `--outputs=west`), whatever the order inputs and outputs are interleaved in.
#[test]
fn ports_keep_declaration_order() {
    let src = "input a: int @ A\noutput x: int @ X\ninput b: Bundle\noutput y: Bundle\ninput c: int @ C\noutput z: int @ Z\n\
               every tick:\n    x = a + c\n    y = b * 2\n    z = a - c\n";
    let anneal = Some(ticky_compiler::place::AnnealOpts { effort: 0.2, ..Default::default() });
    for (poles, outputs_west, anneal) in [(true, false, None), (false, true, None), (true, false, anneal), (false, true, anneal)] {
        let c = compile(src, &Options { poles, outputs_west, anneal, ..opts() }).unwrap();
        let ys = |dir: ticky_syntax::ast::PortDir| -> Vec<f64> {
            c.program.ports.iter().enumerate().filter(|(_, p)| p.dir == dir).map(|(i, _)| c.cg.netlist.entities[c.cg.port_ents[i]].pos.1).collect()
        };
        for dir in [ticky_syntax::ast::PortDir::Input, ticky_syntax::ast::PortDir::Output] {
            let y = ys(dir);
            assert!(y.windows(2).all(|w| w[0] < w[1]), "{dir:?} ports out of order (poles {poles}, west {outputs_west}): {y:?}");
        }
    }
    // E-W: west to east, inputs before outputs in the north row.
    for (outputs_west, anneal) in [(false, None), (true, None), (true, anneal)] {
        let c = compile(src, &Options { ports_ew: true, outputs_west, anneal, ..opts() }).unwrap();
        let pos = |i: usize| c.cg.netlist.entities[c.cg.port_ents[i]].pos;
        let ins: Vec<usize> = (0..c.program.ports.len()).filter(|&i| c.program.ports[i].dir == ticky_syntax::ast::PortDir::Input).collect();
        let outs: Vec<usize> = (0..c.program.ports.len()).filter(|&i| c.program.ports[i].dir == ticky_syntax::ast::PortDir::Output).collect();
        let row: Vec<usize> = if outputs_west { ins.iter().chain(&outs).copied().collect() } else { ins.clone() };
        assert!(row.windows(2).all(|w| pos(w[0]).0 < pos(w[1]).0 && pos(w[0]).1 == pos(w[1]).1), "north row out of order (west {outputs_west})");
        if !outputs_west {
            assert!(outs.windows(2).all(|w| pos(w[0]).0 < pos(w[1]).0), "south row out of order");
            assert!(outs.iter().all(|&o| pos(o).1 > pos(ins[0]).1));
        }
    }
}

/// Runtime signals through function calls (inlined, with a loop) and processes.
#[test]
fn signals_through_functions() {
    let src = r#"input  stock: Bundle
input  go: bool @ G
output best: Signal
output worst: Signal
output n: int @ N

def first_over(b, limit):
    for s, v in b.items(ascending=True):
        if v > limit:
            return s
    return S("signal-0")

def other(s, t, b):
    return t if b[s] < b[t] else s

process p:
    while True:
        wait until go
        best = first_over(stock, 10)
        wait until not go

c = 0
while True:
    wait until go
    worst = other(stock.argmax(), stock.argmin(), stock)
    c += 1
    n = c
    wait until not go

test "functions":
    set stock = {"coal": 5, "stone": 12, "wood": 40}
    set go = 1
    run 60 ticks
    assert best == S("stone") and worst == S("wood") and n == 1
    set go = 0
    set stock = {"coal": 5}
    run 10 ticks
    set go = 1
    run 60 ticks
    assert best == S("signal-0") and worst == S("coal")
"#;
    let c = compile(src, &opts()).unwrap();
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "{:?}", r.failure.map(|d| d.render("t", src)));
    }
}

#[test]
fn screens() {
    let s = |body: &str| format!("import display\ninput c: int @ C\noutput s: display.Screen(4, 3)\n{body}");
    assert!(error_of("output s: display.Screen(4, 3)\n").contains("needs `import display`"));
    assert!(error_of("import graphics\n").contains("no library `graphics`"));
    assert!(error_of("import display\ninput s: display.Screen(4, 3)\n").contains("is an `output`"));
    assert!(error_of("import display\noutput s: display.Screen(100, 100)\n").contains("at most 4096"));
    assert!(error_of("import display\ninput c: int @ C\noutput s: display.Screen(c, 3)\n").contains("positive constants"));
    assert!(error_of(&s("every tick:\n    s.blink()\n")).contains("has no `blink`"));
    assert!(error_of(&s("every tick:\n    s[1, 2, 3] = 1\n")).contains("screen[x, y]"));
    assert!(error_of(&s("every tick:\n    s.rect(1, 2, 3)\n")).contains("expected `screen.rect(x, y, width, height, colour)`"));
    assert!(error_of(&s("every tick:\n    s.text(0, 0, \"a~b\", 1)\n")).contains("the font has no `~`"));
    assert!(error_of(&s("every tick:\n    s.number(0, 0, c, 1)\n")).contains("width=k"));
    assert!(error_of(&s("every tick:\n    s.number(0, 0, c, 1, width=c)\n")).contains("constant number of digits"));
    assert!(error_of(&s("every tick:\n    x = s.rect\n")).contains("is a statement"));
    // Readouts.
    assert!(error_of("import display\ninput d: display.Digits(3)\n").contains("is an `output`"));
    assert!(error_of("import display\noutput d: display.Digits(11)\n").contains("1 to 10 digits"));
    assert!(error_of("import display\ninput c: int @ C\noutput d: display.Digits(2, colour=c)\n").contains("colour must be a constant"));
    let c = compile("import display\ninput c: int @ C\noutput d: display.Digits(3)\nevery tick:\n    d = c * 2\n", &opts()).unwrap();
    assert_eq!(c.cg.screen_lamps[0].len(), 11 * 5);
    let mut h = ticky_compiler::testrun::Harness::new(&c);
    for (v, want) in [(-21, Ok(-42)), (7, Ok(14)), (600, Err("overflow")), (-60, Err("overflow")), (-49, Ok(-98))] {
        h.set(c.program.port_index("c").unwrap(), ticky_compiler::testrun::PVal::Int(v));
        for _ in 0..40 {
            h.sim.step();
        }
        let got = ticky_compiler::display::read_digits(&c.program.screens[0], |k| h.pixel(0, k));
        match want {
            Ok(n) => assert_eq!(got, Ok(n)),
            Err(m) => assert!(got.is_err_and(|e| e.contains(m))),
        }
    }
    // A lamp per pixel, sizes as constants, each pixel on its own signal.
    let c = compile(&s("W = 4\nevery tick:\n    s.fill(c)\n    s[s.width - 1, s.height - 1] = 0xFF0000\n"), &opts()).unwrap();
    assert_eq!(c.cg.screen_lamps[0].len(), 12);
    let mut h = ticky_compiler::testrun::Harness::new(&c);
    h.set(c.program.port_index("c").unwrap(), ticky_compiler::testrun::PVal::Int(0x123456));
    for _ in 0..10 {
        h.sim.step();
    }
    assert_eq!(h.pixel(0, 0), 0x123456);
    assert_eq!(h.pixel(0, 11), 0xFF0000);
    // Writes at constant positions are combined: a full repaint doesn't chain.
    let c = compile(&s("every tick:\n    for i in range(12):\n        s[i] = c + i\n"), &opts()).unwrap();
    assert!(c.cg.blocks[0].depth <= 3, "depth {}", c.cg.blocks[0].depth);
}

#[test]
fn selector_libraries() {
    use ticky_compiler::testrun::{Harness, PVal};
    assert!(error_of("x = items.stack_size(Bundle())\n").contains("needs `import items`"));
    assert!(error_of("import items\nx = items.weight(Bundle())\n").contains("no function `weight`"));
    assert!(error_of("import random\noutput d: int @ D\nevery tick:\n    d = random.randint(1, 0)\n").contains("lo ≤ hi"));
    assert!(error_of("import random\ninput n: int @ N\noutput d: int @ D\nevery tick:\n    d = random.randint(1, n)\n").contains("constant bounds"));
    assert!(error_of("import quality\ninput b: Bundle\noutput o: Bundle\nevery tick:\n    o = quality.set(b, \"shiny\")\n").contains("unknown quality"));
    assert!(error_of("input b: Bundle\noutput o: Bundle\nevery tick:\n    o = {s: v for s, v in b.items() if s.quality > 1 or v > 2}\n").contains("combined with `and`"));
    let nq = Options { quality: false, ..opts() };
    let src = "import quality\ninput b: Bundle\noutput o: Bundle\nevery tick:\n    o = quality.merge(b)\n";
    assert!(compile(src, &nq).is_err_and(|d| d[0].message.contains("needs the Quality mod")));
    // A runtime quality number: one transfer per level, chosen by it.
    let src = "import quality\ninput b: Bundle\ninput q: int @ Q\noutput o: Bundle\nevery tick:\n    o = quality.set(b, q)\n";
    let c = compile(src, &opts()).unwrap();
    let t = ticky_factorio::SignalTable::base();
    let iron = t.lookup("iron-plate").unwrap();
    let mut h = Harness::new(&c);
    h.set(c.program.port_index("b").unwrap(), PVal::Bun(vec![(iron, 5), (t.with_quality(iron, 2), 1)]));
    h.set(c.program.port_index("q").unwrap(), PVal::Int(3));
    for _ in 0..10 {
        h.sim.step();
    }
    assert_eq!(h.get(c.program.port_index("o").unwrap()), PVal::Bun(vec![(t.with_quality(iron, 3), 6)]));
    // Space Age item data differs for a few items.
    let src = "import items\noutput z: int @ Z\nevery tick:\n    z = items.stack_size(S(\"space-science-pack\"))\n";
    for (space_age, want) in [(false, 2000), (true, 200)] {
        let c = compile(src, &Options { space_age, ..opts() }).unwrap();
        let mut h = Harness::new(&c);
        for _ in 0..5 {
            h.sim.step();
        }
        assert_eq!(h.get(c.program.port_index("z").unwrap()), PVal::Int(want));
    }
    // Outputs that depend on random picks are known (the difftest skips them).
    let src = "import random\noutput a: int @ A\noutput b: int @ B\noutput c: int @ C\nx = 0\nevery tick:\n    r = random.randint(1, 6)\n    if r > 3:\n        x += 1\n    a = x\n    b = 4\n    c = r\n";
    let c = compile(src, &opts()).unwrap();
    let mut r: Vec<&String> = c.program.random.iter().filter(|n| ["a", "b", "c"].contains(&n.as_str())).collect();
    r.sort();
    assert_eq!(r, ["a", "c"]);
}

/// Drawing on screens, every pixel against a direct rendering: runtime and constant
/// positions, clipping at the edges, a screen of two banks.
#[test]
fn screen_drawing() {
    use ticky_compiler::display::glyph;
    use ticky_compiler::testrun::{Harness, PVal};
    let (w, h) = (48usize, 32usize); // 1536 pixels: two banks
    let src = format!(
        "import display\ninput x: int @ X\ninput y: int @ Y\ninput n: int @ N\ninput d: int @ D\noutput s: display.Screen({w}, {h})\nevery tick:\n    s.fill(0x111111)\n    s.rect(x, y, 5, 3, 0xFF0000)\n    s.hline(0, 31, 48, 7)\n    s.vline(x, 20, 4, 8)\n    s.digit(y, x, d, 0x00FF00)\n    s.text(x, 25, \"OK!\", 0x0000FF)\n    s.number(30, 2, n, 0xFFFFFF, width=4)\n    s.digit(40, 10, 7, 9)\n"
    );
    let c = compile(&src, &opts()).unwrap_or_else(|d| panic!("{}", d[0].message));
    let mut h_ = Harness::new(&c);
    let port = |n: &str| c.program.port_index(n).unwrap();
    for (x, y, n, d) in [(3, 4, -42, 5), (-2, 30, 12345, 8), (45, -1, 7, 0), (20, 10, -999, 9), (0, 0, 0, 3), (10, 28, -1234, 11)] {
        h_.set(port("x"), PVal::Int(x));
        h_.set(port("y"), PVal::Int(y));
        h_.set(port("n"), PVal::Int(n));
        h_.set(port("d"), PVal::Int(d));
        for _ in 0..60 {
            h_.sim.step();
        }
        // The reference.
        let mut px = vec![0x111111i32; w * h];
        let mut put = |px: &mut Vec<i32>, x: i32, y: i32, c: i32| {
            if (0..w as i32).contains(&x) && (0..h as i32).contains(&y) {
                px[y as usize * w + x as usize] = c;
            }
        };
        let glyph_at = |px: &mut Vec<i32>, put: &mut dyn FnMut(&mut Vec<i32>, i32, i32, i32), gx: i32, gy: i32, bits: i32, c: i32| {
            for i in 0..15 {
                if bits >> i & 1 != 0 {
                    put(px, gx + i % 3, gy + i / 3, c);
                }
            }
        };
        for yy in y..y + 3 {
            for xx in x..x + 5 {
                put(&mut px, xx, yy, 0xFF0000);
            }
        }
        for xx in 0..48 {
            put(&mut px, xx, 31, 7);
        }
        for yy in 20..24 {
            put(&mut px, x, yy, 8);
        }
        if (0..10).contains(&d) {
            glyph_at(&mut px, &mut put, y, x, glyph(char::from_digit(d as u32, 10).unwrap()).unwrap(), 0x00FF00);
        }
        for (i, ch) in "OK!".chars().enumerate() {
            glyph_at(&mut px, &mut put, x + 4 * i as i32, 25, glyph(ch).unwrap(), 0x0000FF);
        }
        // `number`, width 4: right-aligned, minus before the first digit, top glyph all lit
        // when it doesn't fit.
        let text = n.to_string();
        let text = if text.len() > 4 {
            let digits = n.unsigned_abs().to_string();
            format!("#{}", &digits[digits.len() - 3..])
        } else {
            format!("{text:>4}")
        };
        for (i, ch) in text.chars().enumerate() {
            let bits = if ch == '#' { 0x7FFF } else { glyph(ch).unwrap() };
            glyph_at(&mut px, &mut put, 30 + 4 * i as i32, 2, bits, 0xFFFFFF);
        }
        glyph_at(&mut px, &mut put, 40, 10, glyph('7').unwrap(), 9);
        for (k, want) in px.iter().enumerate() {
            assert_eq!(h_.pixel(0, k), *want, "pixel ({}, {}) with x={x} y={y} n={n} d={d}", k % w, k / w);
        }
    }
}

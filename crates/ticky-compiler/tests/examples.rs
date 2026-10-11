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
    // Panels.
    let pn = |body: &str| format!("import display\ninput c: int @ C\noutput p: display.Panel({{\"a\": (\"signal-check\", \"A\"), \"b\": \"B\"}})\n{body}");
    assert!(error_of(&pn("every tick:\n    p = \"zz\"\n")).contains("no message \"zz\""));
    assert!(error_of("import display\noutput p: display.Panel({\"a\": (\"nope-signal\", \"A\")})\n").contains("unknown signal"));
    assert!(error_of("import display\noutput p: display.Panel({})\n").contains("at least one message"));
    assert!(error_of("import display\noutput p: display.Panel({\"a\": \"A\"}, blink=1)\n").contains("no setting `blink`"));
    let c = compile(&pn("every tick:\n    if c > 0:\n        p = \"a\" if c == 1 else \"b\"\n    else:\n        p = 0\n"), &opts()).unwrap();
    assert_eq!(c.cg.netlist.entities.iter().filter(|e| e.kind.proto_name() == "display-panel").count(), 1);
    let mut h = ticky_compiler::testrun::Harness::new(&c);
    for (v, want) in [(1, 1), (2, 2), (0, 0), (1, 1)] {
        h.set(c.program.port_index("c").unwrap(), ticky_compiler::testrun::PVal::Int(v));
        for _ in 0..20 {
            h.sim.step();
        }
        assert_eq!(h.pixel(0, 0), want);
    }
    // Speakers.
    assert!(error_of("output s: speaker.Alarm(\"x\")\n").contains("needs `import speaker`"));
    assert!(error_of("import speaker\noutput s: speaker.Alarm(\"x\", sound=\"moo\")\n").contains("unknown alarm sound"));
    assert!(error_of("import speaker\noutput s: speaker.Notes(\"kazoo\")\n").contains("unknown instrument"));
    assert!(error_of("import speaker\noutput s: speaker.Notes(\"piano\", volume=200)\n").contains("0 to 100"));
    assert!(error_of("import speaker\noutput s: speaker.Alarm(\"x\")\nevery tick:\n    s.play(3)\n").contains("an alarm is a `bool`"));
    // Controls.
    assert!(error_of("output s: controls.Switch(\"x\")\n").contains("needs `import controls`"));
    assert!(error_of("import controls\noutput s: controls.Switch(\"x\")\n").contains("is an `input`"));
    assert!(error_of("import controls\ninput s: controls.Knob(\"x\")\n").contains("has no `Knob`"));
    assert!(error_of("import controls\ninput s: controls.Setting(\"x\")\n").contains("controls.Setting(\"label\", value"));
    assert!(error_of("import controls\ninput s: controls.Switch(\"x\") = port(\"y\")\n").contains("labelled by its first argument"));
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

/// Peripherals at fixed places (`at=`, `Options::at`): where they end up, logic placed around
/// them, overlaps reported.
#[test]
fn fixed_placement() {
    let src = |at: &str| format!("import display\nimport controls\ninput c: int @ C\ninput k: controls.Setting(\"K\", 5{at})\noutput s: display.Screen(8, 3) = port(\"S\"{at})\nevery tick:\n    for i in range(24):\n        s[i] = c * i + k\n");
    for anneal in [None, Some(ticky_compiler::place::AnnealOpts { effort: 0.2, ..Default::default() })] {
        for (x, y) in [(0, 0), (2, 3), (-30, -12), (50, 40)] {
            let o = Options { anneal, at: vec![("s".into(), (x, y)), ("k".into(), (x - 2, y + 6))], ..opts() };
            let c = compile(&src(""), &o).unwrap_or_else(|d| panic!("({x}, {y}): {}", d[0].message));
            assert!(c.cg.netlist.validate(true).is_empty());
            // Pixel 0's lamp is the screen's top-left tile; the control is where it was put.
            let p0 = c.cg.netlist.entities[c.cg.screen_lamps[0][0]].pos;
            assert_eq!(p0, (x as f64 + 0.5, y as f64 + 0.5));
            let k = c.cg.controls[0].1;
            assert_eq!(c.cg.netlist.entities[k].pos, ((x - 2) as f64 + 0.5, (y + 6) as f64 + 0.5));
        }
    }
    // `at=` in the program.
    let c = compile(&src(", at=(4, 7)"), &opts());
    assert!(c.is_err_and(|d| d[0].message.contains("overlaps")), "the control and the screen share a tile");
    let c = compile(&src("").replace("port(\"S\")", "port(\"S\", at=(4, 7))"), &opts()).unwrap();
    assert_eq!(c.cg.netlist.entities[c.cg.screen_lamps[0][0]].pos, (4.5, 7.5));
    // Overlapping the ports west of the grid.
    let o = Options { at: vec![("s".into(), (-6, 0))], ..opts() };
    assert!(compile(&src(""), &o).is_err_and(|d| d[0].message.contains("overlaps the program's ports")));
    let o = Options { at: vec![("nope".into(), (0, 0))], ..opts() };
    assert!(compile(&src(""), &o).is_err_and(|d| d[0].message.contains("no peripheral `nope`")));
}

#[test]
fn signal_conditions_and_inlined_returns() {
    // `if s` / `x if s else y` on Signal state (an `Op::Src`) used to loop forever, and so did
    // choosing between two Signal states; `sig and cond` mixes kinds and is a condition.
    let src = r#"
input  w: Bundle
input  c: int @ C
output t1: Signal
output t2: Signal
output o: Signal
output n: int @ N
output m: int @ M
every 4 ticks:
    o = t1 if c > 0 else t2
    n = 1 if t1 else 0
    m = 1 if t1 and c > 5 else 0
    t1 = w.argmax()
    t2 = w.argmin()

test "signals":
    set w = {"coal": 5, "stone": 2}
    set c = 9
    run 30 ticks
    assert o == S("coal") and n == 1 and m == 1
    set c = 0
    run 30 ticks
    assert o == S("stone") and m == 0
    set w = {}
    run 30 ticks
    assert n == 0 and not o
"#;
    let c = compile(src, &opts()).unwrap_or_else(|d| panic!("{}", d[0].message));
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "test {} failed", r.name);
    }
    // A function's `return` inside `x if c else y` ends inside it: the code after the `if`
    // isn't copied into both arms, so many such calls in a row stay small.
    let mut src = String::from("input a: int @ A\noutput o: int @ O\ndef f(x):\n    return x + 1\nevery 64 ticks:\n    v = a\n");
    for _ in 0..24 {
        src.push_str("    v = f(v) if v > 3 else v - 1\n");
    }
    src.push_str("    o = v\n");
    let c = compile(&src, &opts()).unwrap_or_else(|d| panic!("{}", d[0].message));
    assert!(c.cg.netlist.entities.len() < 400, "{} entities", c.cg.netlist.entities.len());
}

#[test]
fn modded_item_and_recipe_share_a_name() {
    // `S("x", type="recipe")` first used to make every later plain `"x"` the recipe too, so
    // `stock["x"]` read the recipe signal (always 0 on a chest's wire).
    let src = r#"
input  stock: Bundle
output o: int @ O
output r: Signal
R = S("ticky-test-goo", type="recipe")
every tick:
    o = stock["ticky-test-goo"]
    r = R if stock["ticky-test-goo"] > 5 else Bundle().argmax()

test "the item, not the recipe":
    set stock = {"ticky-test-goo": 9}
    run 10 ticks
    assert o == 9 and r == R
"#;
    let c = compile(src, &opts()).unwrap_or_else(|d| panic!("{}", d[0].message));
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "test {} failed", r.name);
    }
    let json = c.blueprint_json().to_string();
    assert!(json.contains(r#""name":"ticky-test-goo","type":"recipe""#) || json.contains(r#""type":"recipe","name":"ticky-test-goo""#));
    let t = ticky_factorio::SignalTable::base();
    let item = t.lookup_kind(ticky_factorio::SignalKind::Item, "ticky-test-goo").expect("the item was added");
    assert_eq!(t.lookup("ticky-test-goo"), Some(item));
}


#[test]
fn optimizations_apply() {
    // Sums of comparisons on the wire, a count over an array (one filter and a total, with
    // the `* 100` pushed into it), and a signal chosen by number (a table lookup). Before
    // these, this block needed 11 ticks and more combinators.
    let src = r#"input  stock: Bundle
input  k: int @ K
output n: int @ N
output r: Signal
output s: int @ S
xs = [0, 0, 0, 0]

every 10 ticks:
    xs[k % 4] = 3
    # A count over an array (one filter and a total), scaled (pushed into the total).
    n = ((1 if xs[0] == 3 else 0) + (1 if xs[1] == 3 else 0) + (1 if xs[2] == 3 else 0) + (1 if xs[3] == 3 else 0)) * 100
    # A choice of signal by number (a table lookup).
    r = S("coal") if k == 1 else S("stone") if k == 2 else S("wood") if k == 3 else Bundle().argmax()
    # A sum of comparisons (on the wire).
    s = (1 if stock["coal"] > 5 else 0) + (1 if stock["stone"] > 5 else 0) - (1 if stock["wood"] > 5 else 0)

test "behaviour":
    set k = 3
    set stock = {"coal": 9, "stone": 9, "wood": 9}
    run 40 ticks
    assert n == 100 and r == S("wood") and s == 1
    set k = 6
    run 40 ticks
    assert n == 200 and r == Bundle().argmax()
"#;
    let c = compile(src, &opts()).unwrap_or_else(|d| panic!("{}", d[0].message));
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "test {} failed", r.name);
    }
    let combinators = c.cg.netlist.entities.iter().filter(|e| matches!(e.kind, ticky_factorio::netlist::Kind::Arith(_) | ticky_factorio::netlist::Kind::Decider(_) | ticky_factorio::netlist::Kind::Selector(_) | ticky_factorio::netlist::Kind::Constant(_))).count();
    assert!(combinators <= 41, "{combinators} combinators (41 when written, ports and controls included)");
    // The running maximum becomes a selector combinator.
    let src = std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/bestof.ticky")).unwrap();
    let c = compile(&src, &opts()).unwrap();
    assert!(c.cg.netlist.entities.iter().any(|e| matches!(e.kind, ticky_factorio::netlist::Kind::Selector(_))));
}

#[test]
fn algebraic_rewrites() {
    // Python `%` shares `r` between its arms (`r + (10 if r < 0 else 0)`); `* 1000 // 10000`
    // of a clamped value is `// 10`; `max(a, 3) > 7` is `a > 7`, and `clamp`'s second test
    // reads its input. 47 combinators before these rewrites.
    let src = r#"input a: int @ A
input b: int @ B
output o: int @ O
output p: int @ P
output q: int @ Q
every 10 ticks:
    o = a % 10 + b
    p = clamp(a, -50, 100) * 1000 // 10000
    q = clamp(b, -5, 5) + (1 if max(a, 3) > 7 else 0)

test "behaviour":
    set a = -17
    set b = 4
    run 30 ticks
    assert o == 7 and p == -2 and q == 4
    set a = 250
    set b = -9
    run 30 ticks
    assert o == -9 and p == 10 and q == -4
"#;
    let c = compile(src, &opts()).unwrap_or_else(|d| panic!("{}", d[0].message));
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "test {} failed", r.name);
    }
    let combinators = c.cg.netlist.entities.iter().filter(|e| matches!(e.kind, ticky_factorio::netlist::Kind::Arith(_) | ticky_factorio::netlist::Kind::Decider(_) | ticky_factorio::netlist::Kind::Selector(_) | ticky_factorio::netlist::Kind::Constant(_))).count();
    assert!(combinators <= 40, "{combinators} combinators (40 when written, ports and controls included)");
}

/// A function with a loop called from one place is inlined there (no subroutine), keeping
/// early returns from inside the loop, waits, globals and its own `i`. A loop variable read
/// only in its loop is the counter itself; an unused one counts down (no register for the
/// end); one read after the loop keeps its last value (or the old one if the loop is empty).
#[test]
fn single_call_inlining_and_loop_counters() {
    let src = r#"input  n: int @ N
output o1: int @ A
output o2: int @ B
output o3: int @ C
output o4: int @ D
output o5: int @ E
output o6: int @ F
output o7: int @ G
output done: bool @ Z

total = 0

def find(limit, x):
    # early return from inside a loop, a wait, a shadowed name, a global write
    global total
    k = 100
    for i in range(limit):
        wait 1
        total += i
        if i * i >= x:
            return i
    return k

def count(m):
    c = 0
    for _ in range(m):
        c += 1
        if c > 50:
            break
    return c

i = 7
o1 = find(n, 10)
o2 = total
o3 = count(n)
# loop variable read after the loop keeps its last value (or the old one when empty)
j = -5
for j in range(n):
    pass
o4 = j
s = 0
for q in range(n, 0, -1):
    if q % 2 == 0:
        continue
    s += q
o5 = s
t = 0
for _ in range(n):
    for _ in range(3):
        t += 1
o6 = t + i
w = 0
for v in range(2, n):
    w = w * 3 + v
o7 = w
done = True

test "n = 5":
    set n = 5
    run until done, max 3000 ticks
    assert o1 == 4 and o2 == 10 and o3 == 5 and o4 == 4 and o5 == 9 and o6 == 22 and o7 == 31

test "n = 0":
    set n = 0
    run until done, max 3000 ticks
    assert o1 == 100 and o2 == 0 and o3 == 0 and o4 == -5 and o5 == 0 and o6 == 7 and o7 == 0

test "n = 2":
    set n = 2
    run until done, max 3000 ticks
    assert o1 == 100 and o2 == 1 and o3 == 2 and o4 == 1 and o5 == 1 and o6 == 13 and o7 == 0
"#;
    let c = compile(src, &opts()).unwrap_or_else(|d| panic!("{}", d[0].message));
    assert!(c.program.subroutines.is_empty(), "{:?}", c.program.subroutines);
    // Counter copies: only `j` (read after its loop). End registers: `i`, `j` and `v`.
    let hidden = |tag: &str| c.program.states.iter().filter(|s| s.name.contains(tag)).map(|s| s.name.clone()).collect::<Vec<_>>();
    assert_eq!(hidden("#k").len(), 1, "{:?}", hidden("#k"));
    assert_eq!(hidden("#end").len(), 3, "{:?}", hidden("#end"));
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "test {} failed: {:?}", r.name, r.failure.map(|d| d.render("t", src)));
    }
    // With `--opt=size`, too (steps are only copied where that removes them).
    for name in ["calculator", "primes", "functions"] {
        let src = std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("../../examples/{name}.ticky"))).unwrap();
        let c = compile(&src, &Options { opt: ticky_compiler::Opt::Size, ..opts() }).unwrap();
        for r in run_tests(&c, &src) {
            assert!(r.failure.is_none(), "{name} (size): test {} failed", r.name);
        }
    }
}

/// Register sharing: variables never live at the same time use one register. `s` keeps its
/// initial value until it's reassigned (and `p`, a copy of it, shares its register); the two
/// loop counters share one; `p` is carried across a wait. Reading a variable before it's
/// assigned is still an error when it could otherwise share.
#[test]
fn registers_are_shared() {
    let src = r#"input  go: bool @ G
output total: int @ T
output prod: int @ P
output done: bool @ D
s = 5
wait until go
t = 0
for i in range(4):
    t += i
    wait 1
total = t + s
p = 1
for j in range(1, 5):
    p *= j
wait 3
s = p
prod = p + s
done = True

test "shared registers":
    set go = True
    run until done, max 200 ticks
    assert total == 11 and prod == 48
"#;
    let c = compile(src, &opts()).unwrap_or_else(|d| panic!("{}", d[0].message));
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "{:?}", r.failure.map(|d| d.render("t", src)));
    }
    // (Registers held under the same conditions share a hold decider: count its parts.)
    let holds: Vec<&str> = c.cg.netlist.entities.iter().filter_map(|e| e.description.as_deref()).flat_map(|d| d.split("; ")).filter(|d| d.starts_with("variable") && d.ends_with("(hold)")).collect();
    // `t`, `s`, one loop counter and the three outputs (9 without sharing).
    assert_eq!(holds.len(), 6, "{holds:?}");
    // A shared register's descriptions name all its variables.
    assert!(holds.contains(&"variable `s` / `p` (hold)") && holds.contains(&"variable `i` / `j` (hold)"), "{holds:?}");
    let e = error_of("input  a: int @ A\noutput o: int @ O\nwait 1\nx = a\no = x\nwait 1\no = y + 1\ny = a + 2\nwait 1\no = y\n");
    assert!(e.contains("`y` might be used before it's assigned"), "{e}");
}

#[test]
fn select_stages() {
    // Selects as stages of deciders: values passed through private wires (`max` 2 deciders,
    // a clamp 3, a positive part 1), both arms computed (two wires), a nested select
    // flattened (3 deciders). 58 combinators before these.
    let src = r#"input  x: int @ X
input  y: int @ Y
output a: int @ A
output b: int @ B
output c: int @ C
output d: int @ D
output e: int @ E

every 10 ticks:
    a = max(x * 3 - y, 7) + 1
    b = min(max(x + y, -5), 20) * 2
    c = ((x - 4) if x - 4 > 0 else 0) + y
    d = ((x * 5) if y > 2 else (y - x)) - 1
    e = (100 if x > 10 else (x * 2 if y < 0 else -3)) + x

test "arms":
    set x = 6
    set y = -3
    run 30 ticks
    assert a == 22 and b == 6 and c == -1 and d == -10 and e == 18
    set x = 1
    set y = 4
    run 30 ticks
    assert a == 8 and b == 10 and c == 4 and d == 4 and e == -2
    set x = 30
    set y = -40
    run 30 ticks
    assert a == 131 and b == -10 and c == -14 and d == -71 and e == 130
    set x = 2
    set y = 30
    run 30 ticks
    assert b == 40 and c == 30 and d == 9 and e == -1
"#;
    let c = compile(src, &opts()).unwrap_or_else(|d| panic!("{}", d[0].message));
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "test {} failed: {:?}", r.name, r.failure);
    }
    let combinators = c.cg.netlist.entities.iter().filter(|e| matches!(e.kind, ticky_factorio::netlist::Kind::Arith(_) | ticky_factorio::netlist::Kind::Decider(_) | ticky_factorio::netlist::Kind::Selector(_) | ticky_factorio::netlist::Kind::Constant(_))).count();
    assert!(combinators <= 50, "{combinators} combinators (50 when written, ports included)");
}

#[test]
fn floor_division_by_constant() {
    // `//` and `%` by a constant: one decider correcting the dividend (on a private wire)
    // and the results, plus the divider(s); `//` and `%` of one dividend share the decider.
    // 49 combinators before this (ports included).
    let src = r#"input  x: int @ X
input  y: int @ Y
output a: int @ A
output b: int @ B
output c: int @ C
output d: int @ D

every 10 ticks:
    a = (x - y) // 7 + 1
    b = (x - y) % 7 + 1
    c = (x + y) // -5 + (x * 3) % -4 + 1
    d = ((x - 3 * y) // 1000 if x > y else 5) + 2

test "floors":
    set x = 5
    set y = 9
    run 30 ticks
    assert a == 0 and b == 4 and c == -3 and d == 7
    set x = -2147483648
    set y = 0
    run 30 ticks
    assert a == -306783378 and b == 6 and c == 429496730 and d == 7
    set x = 3
    set y = -4
    run 30 ticks
    assert a == 2 and b == 1 and c == -2 and d == 2
    set x = 2000
    set y = -999
    run 30 ticks
    assert a == 429 and b == 4 and c == -200 and d == 6
    set x = -14
    set y = 0
    run 30 ticks
    assert a == -1 and b == 1 and c == 1 and d == 7
"#;
    let c = compile(src, &opts()).unwrap_or_else(|d| panic!("{}", d[0].message));
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "test {} failed: {:?}", r.name, r.failure);
    }
    let combinators = c.cg.netlist.entities.iter().filter(|e| matches!(e.kind, ticky_factorio::netlist::Kind::Arith(_) | ticky_factorio::netlist::Kind::Decider(_) | ticky_factorio::netlist::Kind::Selector(_) | ticky_factorio::netlist::Kind::Constant(_))).count();
    assert!(combinators <= 44, "{combinators} combinators (44 when written, ports included)");
}

#[test]
fn pipelines_share_delays() {
    // Values needed several ticks after they're computed come off shared carry wires (one
    // combinator per tick for the whole block, not a delay chain per value), the sums are on
    // the wire and the start-up delay is a counter. Before these: 50 combinators in the
    // block, latency 11.
    let src = r#"input  x: int @ X
input  y: int @ Y
output s: int @ S
output last: int @ L
output tot: int @ T
last = 0
tot = 0
every tick:
    p = x * y
    q = (x - y) * (x + y)
    s = (p > 10) + (q > 2) - (x > y) + p * 2 - q
    if s > 50 and x > 0:
        last = s + y
    tot += s
"#;
    let c = compile(src, &opts()).unwrap_or_else(|d| panic!("{}", d[0].message));
    let b = &c.cg.blocks[0];
    assert!(b.combinators <= 25 && b.latency == Some(8), "{} combinators, latency {:?}", b.combinators, b.latency);
    let desc = |e: &ticky_factorio::netlist::Entity| e.description.clone().unwrap_or_default();
    assert!(c.cg.netlist.entities.iter().any(|e| desc(e).contains("carry 2")));
    assert!(c.cg.netlist.entities.iter().any(|e| desc(e).contains("start-up counter")));
    // Inputs that change every tick: every output is the value for the inputs `latency`
    // ticks earlier, all from the same iteration, and a restart after RUN off is exactly
    // like the first start.
    use ticky_compiler::testrun::{Harness, PVal};
    let port = |n: &str| c.program.port_index(n).unwrap();
    let int = |v: PVal| match v {
        PVal::Int(k) => k,
        PVal::Bun(_) => unreachable!(),
    };
    let input = |t: i64| (((t * 7) % 13) as i32 - 4, ((t * 5) % 11) as i32 - 3);
    let f = |(x, y): (i32, i32)| {
        let (p, q) = (x * y, (x - y) * (x + y));
        (p > 10) as i32 + (q > 2) as i32 - (x > y) as i32 + p * 2 - q
    };
    let mut h = Harness::new(&c);
    let drive = |h: &mut Harness, ticks: i64| -> Vec<[i32; 3]> {
        (0..ticks)
            .map(|t| {
                let (x, y) = input(t);
                h.set(port("x"), PVal::Int(x));
                h.set(port("y"), PVal::Int(y));
                h.sim.step();
                [int(h.get(port("s"))), int(h.get(port("last"))), int(h.get(port("tot")))]
            })
            .collect()
    };
    let first = drive(&mut h, 120);
    let lat = (0..30).find(|&l| (40..120).all(|t| first[t as usize][0] == f(input(t - l)))).expect("s follows the inputs");
    let (mut last, mut tot) = (0, 0);
    let start = (0..120).find(|&t| first[t][2] != 0).unwrap();
    for (t, row) in first.iter().enumerate().skip(start) {
        let (x, y) = input(t as i64 - lat);
        if row[0] > 50 && x > 0 {
            last = row[0] + y;
        }
        tot += row[0];
        assert_eq!((row[1], row[2]), (last, tot), "registers at tick {t}");
    }
    h.sim.set_constant_on(c.cg.run_switch, false);
    h.set(port("x"), PVal::Int(0));
    h.set(port("y"), PVal::Int(0));
    for _ in 0..30 {
        h.sim.step();
    }
    h.sim.set_constant_on(c.cg.run_switch, true);
    assert_eq!(drive(&mut h, 120), first);
}

#[test]
fn registers_share_and_increment() {
    // Increments (`c += 1` under a condition, `t += a`, a reset), holds shared between
    // registers and samples, staged inputs (`a`, `b`: only main samples them, one load) and
    // two blocks of the same period on one clock.
    let src = r#"input  a: int @ A
input  b: int @ B
output total: int @ T
output count: int @ C
output ticks1: int @ X
output ticks2: int @ Y
x1 = 0
x2 = 5

every 10 ticks:
    x1 += 1
    ticks1 = x1

every 10 ticks:
    x2 = x2 - 1
    ticks2 = x2

t = 0
c = 0
while True:
    t += a
    if b > 0:
        c += 1
    if t > 100:
        t = 0
    total = t
    count = c

test "behaviour":
    set a = 7
    set b = 1
    run 60 ticks
    assert ticks1 >= 5 and ticks2 == 5 - ticks1 and total > 0 and count > 0
    set b = 0
    run 200 ticks
    assert total <= 100 and ticks1 + ticks2 == 5
"#;
    let c = compile(src, &opts()).unwrap_or_else(|d| panic!("{}", d[0].message));
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "test {} failed: {:?}", r.name, r.failure);
    }
    let descs: Vec<&str> = c.cg.netlist.entities.iter().filter_map(|e| e.description.as_deref()).collect();
    let has = |s: &str| descs.iter().filter(|d| d.contains(s)).count();
    assert_eq!(has("clock, period 10"), 1, "one shared clock");
    assert!(has("(increment)") >= 3, "increments: {descs:?}");
    assert_eq!(has("samples of main: inputs (load)"), 1, "staged inputs");
    assert!(descs.iter().any(|d| d.contains("(hold); ") && d.contains("sample of")), "shared holds: {descs:?}");
}

/// Range comprehensions of arithmetic in the range variable are bundle operations on the
/// position table (expand/vectorize.rs), with Python's floor `%` and `//` (negative divisor
/// too) and ranges with a start and step; an array assigned from one is a signal array.
/// The report counts 216 combinators unrolled, 72 vectorised.
#[test]
fn vectorised_range_comprehensions() {
    let src = r#"input  s: int @ S
input  i: int @ I
output a: int @ A
output b: int @ B
output c: int @ C
output d: int @ D
every 30 ticks:
    xs = [(k * s) % 41 - 20 for k in range(16)]
    ys = [(k * s + 7) // -6 for k in range(-9, 30, 3)]
    a = xs[i % 16]
    b = sum(xs)
    c = ys[i % len(ys)]
    d = sorted(ys)[2]

test "behaviour":
    set s = 7
    set i = 5
    run 100 ticks
    assert a == 15 and b == -54 and c == -9 and d == -26
    set s = -123456
    set i = 11
    run 100 ticks
    assert a == 7 and b == -18 and c == 493822 and d == -61730
    set s = 2000000
    set i = 3
    run 100 ticks
    assert a == -1 and b == 71 and c == -2 and d == -7000002
"#;
    let c = compile(src, &opts()).unwrap_or_else(|d| panic!("{}", d[0].message));
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "test {} failed", r.name);
    }
    let combinators = c.cg.netlist.entities.iter().filter(|e| matches!(e.kind, ticky_factorio::netlist::Kind::Arith(_) | ticky_factorio::netlist::Kind::Decider(_) | ticky_factorio::netlist::Kind::Selector(_) | ticky_factorio::netlist::Kind::Constant(_))).count();
    assert!(combinators <= 82, "{combinators} combinators (82 when written, ports included)");
}

#[test]
fn sorting_networks_become_ranks() {
    // A hand-written sort's used outputs (scalars, a state array's slots, values never
    // negative), and min/max trees that are order statistics, as selector ranks; a tree that
    // isn't one (`mix`) stays. Zeros, duplicates and the ends of the range included.
    // `ticky check` counted 186 combinators before this, 97 after.
    let src = r#"input  a: int @ A
input  b: int @ B
input  c: int @ C
input  d: int @ D
input  e: int @ E
output med: int @ M
output second: int @ S
output low: int @ L
output mix: int @ X
output small: int @ Q

hist = [0] * 4
n = 0

def sort(xs):
    for i in range(len(xs) - 1):
        for j in range(len(xs) - 1 - i):
            if xs[j] > xs[j + 1]:
                t = xs[j]
                xs[j] = xs[j + 1]
                xs[j + 1] = t
    return xs

every 30 ticks:
    med = sort([a, b, c, d, e])[2]
    hist[n % 4] = a
    n += 1
    second = sort(hist)[1]
    low = min(max(a, b), max(c, d), max(a, e))
    mix = max(min(a, b), min(c, d))
    small = sort([a & 1023, b & 1023, c & 1023, d & 1023])[1]

test "order statistics":
    set a = 5
    set b = -3
    set c = 0
    set d = 5
    set e = 2147483647
    run 150 ticks
    assert med == 5 and second == 5 and low == 5 and mix == 0 and small == 5
    set a = -2147483648
    set b = 0
    set c = 0
    set d = -7
    set e = 9
    run 150 ticks
    assert med == 0 and second == -2147483648 and low == 0 and mix == -7 and small == 0
    set a = 4
    set b = 4
    set c = -1
    set d = 1023
    set e = -1
    run 150 ticks
    assert med == 4 and second == 4 and low == 4 and mix == 4 and small == 4
"#;
    let c = compile(src, &opts()).unwrap_or_else(|d| panic!("{}", d[0].message));
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "test {} failed: {:?}", r.name, r.failure);
    }
    let combinators = c.cg.netlist.entities.iter().filter(|e| matches!(e.kind, ticky_factorio::netlist::Kind::Arith(_) | ticky_factorio::netlist::Kind::Decider(_) | ticky_factorio::netlist::Kind::Selector(_) | ticky_factorio::netlist::Kind::Constant(_))).count();
    assert!(combinators <= 100, "{combinators} combinators (100 when written, ports included)");
}

#[test]
fn staged_loads() {
    // Values used only by one load are computed under the register's own signal onto a
    // staging wire: a guarded one is one decider (`max(a - b, 0)`: its guards test the value
    // on the wire), loads committing together share one, increments too.
    let src = r#"input  a: int @ A
input  b: int @ B
output m: int @ M
output y: int @ Y
output p: int @ P
output q: int @ Q
output z: int @ Z
output c: int @ C
y = 7
c = 0
every 5 ticks:
    m = max(a - b, 0)
    if a > 3:
        y = a * 2 + b

p = 0
q = 0
while True:
    p = a + 1
    q = b * 3
    z = a // 4
    wait 3 ticks
    c += a * b
    q = a - b

test "behaviour":
    set a = 9
    set b = -3
    run 40 ticks
    assert m == 12 and y == 15 and p == 10 and z == 2 and c < 0
    set a = -7
    set b = 2
    run 40 ticks
    assert m == 0 and y == 15 and p == -6 and z == -2 and (q == 6 or q == -9)
"#;
    let c = compile(src, &opts()).unwrap_or_else(|d| panic!("{}", d[0].message));
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "test {} failed: {:?}", r.name, r.failure);
    }
    let descs: Vec<&str> = c.cg.netlist.entities.iter().filter_map(|e| e.description.as_deref()).collect();
    let has = |s: &str| descs.iter().filter(|d| d.contains(s)).count();
    assert_eq!(has("(load condition)"), 0, "guarded loads need no enable decider: {descs:?}");
    assert!(
        descs.iter().any(|d| d.contains("`p` (staged load)") && d.contains("`q` (staged load)") && d.contains("`z` (staged load)")),
        "one decider loads p, q and z: {descs:?}"
    );
    assert_eq!(has("`m` (staged load)"), 1);
    assert_eq!(has("`c` (staged increment)"), 1);
}

/// Tuple assignments to array elements and variables: every value is taken before the first
/// store, even when a value is just a name (an element at an index that is constant once the
/// loop unrolls, or a variable that an earlier target assigns), in `every` blocks, the main
/// program, nested and `while` loops, and on bundle signals; and before a later value's call
/// can change them.
#[test]
fn tuple_assignments_take_values_first() {
    let every = r#"input a: int @ A
input b: int @ B
output o0: int @ X
output o1: int @ Y
output o2: int @ Z
output o3: int @ W
output o4: int @ V
output o5: int @ U
output o6: int @ T
output o7: int @ S

def swap2(ys, i):
    ys[i], ys[i + 1] = ys[i + 1], ys[i]
    return ys

every 30 ticks:
    xs = [a, b, a + b]
    for j in range(1):
        xs[0], xs[j + 1] = xs[j + 1], xs[0]
    o0 = xs[0] * 100 + xs[1]
    ys = [a, b, 7]
    for i in range(2):
        for j in range(2 - i):
            if ys[j] > ys[j + 1]:
                ys[j], ys[j + 1] = ys[j + 1], ys[j]
    o1 = ys[0] * 10000 + ys[1] * 100 + ys[2]
    zs = [a, b]
    m = 9
    for j in range(1):
        m, zs[j] = zs[j], m
    o2 = m * 100 + zs[0]
    ws = [a, b]
    n = 0
    for j in range(1):
        zs[j], n = n + 4, zs[j + 1]
        ws[(n + 10) % 2], ws[1 - (n + 10) % 2] = ws[1], ws[0]
    o3 = zs[0] * 100 + n
    o4 = ws[0] * 100 + ws[1]
    vs = [a, b, 3]
    for j in range(2):
        vs[j], vs[j + 1], vs[2 - j] = vs[j + 1], vs[2 - j], vs[j]
    o5 = vs[0] * 10000 + vs[1] * 100 + vs[2]
    k = 0
    us = [a, b]
    for j in range(1):
        k, us[k] = 1, 50
    o6 = us[0] * 100 + us[1] + k * 1000000
    ts = swap2([a, b, 1], 1)
    o7 = ts[0] * 10000 + ts[1] * 100 + ts[2]

test "swaps":
    set a = 5
    set b = -3
    run 100
    assert o0 == -295
    assert o1 == -29493
    assert o2 == 509
    assert o3 == 397
    assert o4 == 497
    assert o5 == -29697
    assert o6 == 1000550
    assert o7 == 50097
"#;
    let main = every.replace("every 30 ticks:\n", "while True:\n    wait 30\n").replace("run 100", "run 1000");
    let misc = r#"input a: int @ A
input b: int @ B
input s: Bundle
output o0: int @ X
output o1: int @ Y
output o2: int @ Z
output o3: Bundle

every 30 ticks:
    c = s
    for q in range(1):
        c["iron-plate"], c["copper-plate"] = c["copper-plate"], c["iron-plate"] + q
    o3 = c
    t = 0
    for q in range(2):
        t, c["coal"] = c["coal"] + q, t
    o2 = t * 100 + c["coal"]

while True:
    xs = [a, b, 1, 2]
    j = 0
    while j < 3:
        if xs[j] > xs[j + 1]:
            xs[j], xs[j + 1] = xs[j + 1], xs[j]
        j += 1
    o0 = xs[3] * 100 + xs[0]
    ys = [a, b]
    for k in range(2):
        for j in range(1):
            ys[j], ys[k] = ys[1 - k], ys[j]
    o1 = ys[0] * 100 + ys[1]
    wait 5

test "misc":
    set a = 5
    set b = -3
    set s = {"iron-plate": 10, "copper-plate": 20, "coal": 3}
    run 1000
    assert o0 == 497
    assert o1 == 505
    assert o3["iron-plate"] == 20 and o3["copper-plate"] == 10
    assert o2 == 103
"#;
    // A later value's call changes what an earlier value read (tuples and lists alike).
    let calls = "output o0: int @ A\noutput o1: int @ B\noutput o2: int @ C\noutput o3: int @ E\n\
                 arr = [3, -1, 4, 1]\ndef f(p):\n    arr[0] = p\n    return 1\n\
                 arr[1], arr[2] = arr[0] + 10, f(7) + arr[0]\no0 = arr[1]\no1 = arr[2]\n\
                 b = 0\narr[b], b = arr[3] * 2, f(9)\nys = [arr[0] - 1, f(4)]\no2 = arr[0] * 100 + arr[1]\no3 = ys[0]\n\
                 test \"t\":\n    run 300 ticks\n    assert o0 == 13 and o1 == 8 and o2 == 413 and o3 == 1\n";
    for src in [every, main.as_str(), misc, calls] {
        let c = compile(src, &opts()).unwrap();
        for r in run_tests(&c, src) {
            assert!(r.failure.is_none(), "{:?}", r.failure.map(|d| d.render("t", src)));
        }
    }
}

#[test]
fn lookup_rewrites_apply() {
    // A pick among bundle reads by a runtime index (one-hot lookup + one `b · onehot`,
    // sharing the array write's index wire), a signal table keyed by a number (no index
    // arithmetic), a scaled count (one decider), and a condition reading a bundle's signals
    // straight off its wire.
    let src = r#"input  a: Bundle
input  b: Bundle
input  i: int @ I
input  y: int @ Y
output p: int @ P
output r: Signal
output n: int @ N
output c: int @ C
xs = [0, 0, 0, 0]

every 10 ticks:
    xs[i % 4] = 5
    p = [a["coal"], a["stone"], a["wood"], a["iron-plate"]][i % 4] * 100 + xs[i % 4]
    r = S("coal") if y == 1 else S("stone") if y == 2 else S("wood") if y == 3 else Bundle().argmax()
    n = 300 * ((1 if b["coal"] == 2 else 0) + (1 if b["stone"] == 2 else 0) + (1 if b["wood"] == 2 else 0)) - y
    c = (7 if b["iron-plate"] == y and b["copper-plate"] < 3 else -1) * i

test "behaviour":
    set a = {"coal": 1, "stone": 2, "wood": 3, "iron-plate": 4}
    set b = {"coal": 2, "wood": 2, "iron-plate": 3}
    set i = 2
    set y = 3
    run 40 ticks
    assert p == 305 and r == S("wood") and n == 597 and c == 14
    set i = 7
    set y = 0
    run 40 ticks
    assert p == 405 and r == Bundle().argmax() and n == 600 and c == -7
"#;
    let c = compile(src, &opts()).unwrap_or_else(|d| panic!("{}", d[0].message));
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "test {} failed", r.name);
    }
    let ents = &c.cg.netlist.entities;
    let made = |what: &str| ents.iter().filter(|e| e.description.as_deref().is_some_and(|d| d.ends_with(what))).count();
    assert_eq!(made("read a signal's value"), 1, "the pick is one dot product");
    assert_eq!(made("filter and total"), 1, "the count is one decider");
    assert_eq!(made("block 1: index"), 1, "one index wire, shared by the pick and the array");
    assert_eq!(made("read one signal"), 0, "no separate reads");
    let combinators = ents.iter().filter(|e| e.kind.is_combinator()).count();
    assert!(combinators <= 47, "{combinators} combinators (47 when written, 58 before these rewrites)");
}

/// A function calling 20 inlined functions with early `return`s: flattening it into one step
/// would copy its tail 2^20 times ("too much branching" before; 8 calls already gave 4,382
/// combinators). Past a budget it becomes steps instead.
#[test]
fn early_returns_dont_multiply_code() {
    let src = r#"input x: int @ X
input y: int @ Y
output o: int @ O
output done: bool @ D
arr = [3, -1, 4, 1]
def f(p, q):
    arr[p % 4] = q
    if p > 2:
        return q + arr[1]
    return q * 2 - arr[0]
def g(p, q):
    q = f(p + 0, q)
    q = f(p + 1, q)
    q = f(p + 2, q)
    q = f(p + 3, q)
    q = f(p + 4, q)
    q = f(p + 5, q)
    q = f(p + 6, q)
    q = f(p + 7, q)
    q = f(p + 8, q)
    q = f(p + 9, q)
    q = f(p + 10, q)
    q = f(p + 11, q)
    q = f(p + 12, q)
    q = f(p + 13, q)
    q = f(p + 14, q)
    q = f(p + 15, q)
    q = f(p + 16, q)
    q = f(p + 17, q)
    q = f(p + 18, q)
    q = f(p + 19, q)
    return q
o = g(x, y) + g(y, x)
done = True

test "a":
    set x = 1
    set y = 2
    run until done, max 5000 ticks
    assert o == -933125

test "b":
    set x = -30
    set y = 5
    run until done, max 5000 ticks
    assert o == -93739
"#;
    let c = compile(src, &opts()).unwrap_or_else(|d| panic!("{}", d[0].message));
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "test {} failed: {:?}", r.name, r.failure.map(|d| d.render("t", src)));
    }
    let n = c.cg.netlist.entities.iter().filter(|e| e.kind.is_combinator()).count();
    assert!(n < 1000, "{n} combinators");
}

#[test]
fn passed_values_of_one_array_element() {
    // An unrolled loop writes `arr[0]` through a select in each iteration. Each select passes
    // its arms' values on a private wire under its own name, which was the array element's
    // signal (written straight onto the array's wire), so two iterations' passes added up on
    // one cluster wire (arr[0] came out 3 instead of 1 for x = y = -20). Found by fuzz_level2.
    let src = r#"input x: int @ X
input y: int @ Y
output o0: int @ A
output o1: int @ B
output o2: int @ C
output o3: int @ E
output o4: int @ F
output o5: int @ G
output o6: int @ H
output done: bool @ D
every 1000 ticks:
    arr = [3, -1, 4, 1]
    a = 0
    b = 1
    c = 2
    for i4 in range(3):
        arr[x % 4] = a
        a = y
        u1 = (arr[3] if x else arr[0])
        u3 = max(arr) & c
        arr[0] = u1
        arr[i4 + 1] = 0
        arr[1] = u3
    o0 = a
    o1 = b
    o2 = c
    o3 = arr[0]
    o4 = arr[1]
    o5 = arr[2]
    o6 = arr[3]
    done = True

test "x=-20, y=-20":
    set x = -20
    set y = -20
    run 1100 ticks
    assert o0 == -20 and o3 == 1 and o4 == 0 and o5 == 0 and o6 == 0

test "x=5, y=3":
    set x = 5
    set y = 3
    run 1100 ticks
    assert o0 == 3 and o3 == 1 and o4 == 2 and o5 == 0 and o6 == 0

test "x=0, y=7":
    set x = 0
    set y = 7
    run 1100 ticks
    assert o0 == 7 and o3 == 7 and o4 == 2 and o5 == 0 and o6 == 0

test "x=2, y=-9":
    set x = 2
    set y = -9
    run 1100 ticks
    assert o0 == -9 and o3 == 1 and o4 == 2 and o5 == -9 and o6 == 0
"#;
    let c = compile(src, &opts()).unwrap_or_else(|d| panic!("{}", d[0].message));
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "{:?}", r.failure.map(|d| d.render("t", src)));
    }
}

#[test]
fn staged_select_and_bundle_write_of_one_cluster() {
    // `c`'s select is staged (computed under its register's signal onto a staging wire) and
    // `arr[3]`'s writes the array element's signal straight into the bundle: both name their
    // passed values on the cluster's wire after those signals, which were the same one, so
    // the passes added up (arr[3] came out a + c = -1 for x = -6, y = -17). Found by
    // fuzz_level2 seed 61.
    let src = r#"input x: int @ X
input y: int @ Y
output o0: int @ A
output o1: int @ B
output o2: int @ C
output o3: int @ E
output o4: int @ F
output o5: int @ G
output o6: int @ H
output done: bool @ D
if True:
    arr = [0, 0, 0, 0]
    a = 0
    b = 5
    c = 2
    if y:
        a = b
        arr[y % 4] = a
        c = x if x else x % y
    arr[2], arr[3] = (1, a if x else 9)
    o0 = a
    o1 = b
    o2 = c
    o6 = arr[3]
    done = True

test "x=-6, y=-17":
    set x = -6
    set y = -17
    run 20 ticks
    assert o0 == 5 and o2 == -6 and o6 == 5

test "x=3, y=2":
    set x = 3
    set y = 2
    run 20 ticks
    assert o0 == 5 and o2 == 3 and o6 == 5

test "x=0, y=5":
    set x = 0
    set y = 5
    run 20 ticks
    assert o0 == 5 and o2 == 0 and o6 == 9
"#;
    let c = compile(src, &opts()).unwrap_or_else(|d| panic!("{}", d[0].message));
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "{:?}", r.failure.map(|d| d.render("t", src)));
    }
}

#[test]
fn stage_of_a_flattened_select_left_unread() {
    // `f0`'s inlined selects under the same condition flatten into the outer one, which
    // leaves an inner select (and the stage planned for it) unread. Its passes were still
    // put on its cluster's wire, which it doesn't have: a panic. Found by fuzz_level2 seed 65.
    let src = r#"input x: int @ X
input y: int @ Y
output o1: int @ B
output o2: int @ C
arr = [3, -1, 4, 1]
b = 1
def f0(p, q):
    if arr[3]:
        return p - arr[q % 4]
    return sum(arr) * q
b, arr[2], b = y, 0, b
c = f0(f0(y, y) or b, x) if y else 3
o1 = b
o2 = c

test "x=0, y=0":
    run 30 ticks
    assert o1 == 1 and o2 == 3

test "x=3, y=-2":
    set x = 3
    set y = -2
    run 30 ticks
    assert o1 == 1 and o2 == -3

test "x=-5, y=7":
    set x = -5
    set y = 7
    run 30 ticks
    assert o1 == 1 and o2 == 5
"#;
    let c = compile(src, &opts()).unwrap_or_else(|d| panic!("{}", d[0].message));
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "{:?}", r.failure.map(|d| d.render("t", src)));
    }
}

#[test]
fn hold_of_many_writers_with_direct_loads() {
    // Each step loads `a` under a condition the load decider checks itself, so the hold has
    // a factor "not committing, or the condition fails" per step. Distributed, that was 2^20
    // terms: a decider of millions of conditions (found as a fuzz_procs program that
    // wouldn't build or simulate). Past a few terms the hold is one term per writer's term.
    let mut src = String::from("input x: int @ X\noutput o: int @ A\na = 0\n");
    for i in 1..=20 {
        src += &format!("if x > {i}:\n    a = {}\nwait 2\n", 3 * i);
    }
    src += "o = a\n";
    for (x, o) in [(-3, 0), (1, 0), (2, 3), (7, 18), (20, 57), (50, 60)] {
        src += &format!("\ntest \"x={x}\":\n    set x = {x}\n    run 200 ticks\n    assert o == {o}\n");
    }
    let c = compile(&src, &opts()).unwrap_or_else(|d| panic!("{}", d[0].message));
    let most = c.cg.netlist.entities.iter().filter_map(|e| match &e.kind {
        ticky_factorio::netlist::Kind::Decider(d) => Some(d.conds.len()),
        _ => None,
    });
    let most = most.max().unwrap();
    assert!(most <= 102, "a decider with {most} conditions (102: [ST=0, RUN≠0] and 20 commit pulses = 0, then 4 per step)");
    for r in run_tests(&c, &src) {
        assert!(r.failure.is_none(), "{:?}", r.failure.map(|d| d.render("t", &src)));
    }
}

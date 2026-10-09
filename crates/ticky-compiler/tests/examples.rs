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
        let c = compile(&src, &opts()).unwrap_or_else(|d| {
            panic!("{}", d.iter().map(|d| d.render(&name, &src)).collect::<String>())
        });
        assert!(c.cg.netlist.validate(true).is_empty());
        // The placement options give valid layouts too.
        let other = Options { poles: false, outputs_west: true, quality: false, ..opts() };
        let c2 = compile(&src, &other).unwrap_or_else(|d| panic!("{name} (no poles, west outputs): {}", d[0].message));
        assert!(c2.cg.netlist.validate(false).is_empty());
        assert_eq!(c2.layout.poles, 0);
        // So does the experimental annealing placement, deterministically.
        let a = ticky_compiler::place::AnnealOpts { effort: 0.2, ..Default::default() };
        let annealed = Options { anneal: Some(a), ..opts() };
        let c3 = compile(&src, &annealed).unwrap_or_else(|d| panic!("{name} (annealed): {}", d[0].message));
        assert!(c3.cg.netlist.validate(true).is_empty(), "{name} (annealed)");
        assert_eq!(compile(&src, &annealed).unwrap().blueprint_string(), c3.blueprint_string(), "{name}: annealing isn't deterministic");
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
}

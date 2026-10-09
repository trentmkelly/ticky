//! Compiles every example program, checks its layout and runs its `test` blocks.

use std::path::Path;

use ticky_compiler::testrun::run_tests;
use ticky_compiler::{compile, Options};

fn opts() -> Options {
    Options { autostart: false, label: "test".into(), opt: Default::default() }
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
        assert!(c.cg.netlist.validate().is_empty());
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
    assert!(error_of("output y: int @ nonsense_signal\n").contains("unknown signal"));
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
    assert!(error_of("for i in range(0, 10, 0):\n    pass\n").contains("can't be 0"));
}

#[test]
fn constants_fold_away() {
    let src = "K = 6 * 7\nW = K // 4 - -3 % 2\noutput y: int @ Y\nevery tick:\n    y = W + 0\n";
    let c = compile(src, &opts()).unwrap();
    assert_eq!(c.program.consts["W"], 9);
    // y = 9 is loaded with a constant: no arithmetic combinators in the block.
    assert_eq!(c.cg.blocks[0].depth, 0);
}

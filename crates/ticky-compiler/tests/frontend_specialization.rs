use ticky_compiler::testrun::{run_tests, Harness, PVal};
use ticky_compiler::{compile, Compiled, Opt, Options};

fn build(src: &str, opt: Opt, checks: bool) -> Compiled {
    let c = compile(src, &Options { opt, checks, ..Default::default() })
        .unwrap_or_else(|d| panic!("{}", d.iter().map(|d| d.render("probe", src)).collect::<String>()));
    assert!(c.cg.netlist.validate(true).is_empty());
    for result in run_tests(&c, src) {
        assert!(result.failure.is_none(), "{}: {:?}", result.name, result.failure);
    }
    c
}

fn count(c: &Compiled) -> usize {
    c.cg.netlist.entities.iter().filter(|e| e.kind.proto_name().ends_with("combinator")).count()
}

const PORTS: &str = "input x: int @ X\noutput y: int @ Y\n";

#[test]
fn constant_loop_call_folds_outside_prologue() {
    let src = format!("{PORTS}def calc(n):\n    a = 0\n    for i in range(n):\n        a += i * i\n    return a\nwhile True:\n    y = x + calc(10)\n    wait 1\ntest \"value\":\n    set x = -300\n    run 100 ticks\n    assert y == -15\n    set x = 7\n    run 100 ticks\n    assert y == 292\n");
    for opt in [Opt::Size, Opt::Speed] {
        let c = build(&src, opt, false);
        let direct = build(&format!("{PORTS}while True:\n    y = x + 285\n    wait 1\n"), opt, false);
        assert_eq!(count(&c), count(&direct));
    }
}

#[test]
fn outlines_large_closed_function_only_for_size() {
    let rounds: String = (0..6).map(|i| format!("    a = (a * {}) ^ (a >> {})\n", 13 + 2 * i, 1 + i % 4)).collect();
    let src = format!(
        "{PORTS}def mix(a):\n{rounds}    return a\nwhile True:\n    y = mix(x)\n    wait 1\n    y = mix(x + 1)\n    wait 1\n    y = mix(x + 2)\n    wait 1\n"
    );
    let size = build(&src, Opt::Size, false);
    let speed = build(&src, Opt::Speed, false);
    assert!(size.program.subroutines.contains("mix"));
    assert!(!speed.program.subroutines.contains("mix"));
    assert!(count(&size) + 15 <= count(&speed), "{} vs {}", count(&size), count(&speed));
    let expected: Vec<i32> = (7i32..10)
        .map(|mut a| {
            for i in 0..6 {
                a = a.wrapping_mul(13 + 2 * i) ^ (a >> (1 + i % 4));
            }
            a
        })
        .collect();
    for c in [&size, &speed] {
        let mut h = Harness::new(c);
        h.set(0, PVal::Int(7));
        let mut changes = Vec::new();
        for _ in 0..200 {
            h.sim.step();
            if let PVal::Int(y) = h.get(1) {
                if y != 0 && changes.last() != Some(&y) {
                    changes.push(y);
                }
            }
        }
        assert!(changes.len() >= 3, "{changes:?}");
        assert_eq!(&changes[..3], expected);
    }
    // A raw source-size heuristic would outline this, despite folding to zero.
    let dead = src.replace("(a *", "(0 *");
    assert!(!build(&dead, Opt::Size, false).program.subroutines.contains("mix"));
    let adjacent = src.replace("    y = mix", "    snapshot = x\n    y = mix");
    assert!(!build(&adjacent, Opt::Size, false).program.subroutines.contains("mix"));
    // A call buried inside an expression must not move the neighboring input sample.
    let nested = src.replace("y = mix(x", "y = x + mix(x");
    assert!(!build(&nested, Opt::Size, false).program.subroutines.contains("mix"));
}

#[test]
fn small_private_loop_unrolls_only_when_profitable() {
    let src = format!("{PORTS}while True:\n    a = x\n    for i in range(3):\n        a = a * 2 + 1\n    y = a\n    wait 1\ntest \"values\":\n    set x = -5\n    run 100 ticks\n    assert y == -33\n    set x = 268435456\n    run 100 ticks\n    assert y == -2147483641\n");
    let size = build(&src, Opt::Size, false);
    let speed = build(&src, Opt::Speed, false);
    assert!(count(&size) + 4 <= count(&speed));
    let large = src.replace("range(3)", "range(30)").split("test ").next().unwrap().to_string();
    let large_size = build(&large, Opt::Size, false);
    assert!(large_size.program.procs[0].steps.len() > size.program.procs[0].steps.len());
}

#[test]
fn preserves_sampling_observable_writes_waits_and_loop_index() {
    for body in [
        "    a = x\n    for i in range(3):\n        a = a * 2 + 1\n    y = a + x\n",
        "    a = 0\n    for i in range(3):\n        a += x\n    y = a\n",
        "    for i in range(3):\n        y += 1\n",
        "    a = x\n    for i in range(3):\n        a += 1\n        wait 2\n    y = a\n",
        "    a = x\n    i = 0\n    for i in range(3):\n        a += 1\n    y = a + i\n",
    ] {
        let src = format!("{PORTS}while True:\n{body}    wait 1\n");
        let size = build(&src, Opt::Size, false);
        let speed = build(&src, Opt::Speed, false);
        let mut a = Harness::new(&size);
        let mut b = Harness::new(&speed);
        for tick in 0..100 {
            let x = PVal::Int(tick % 7 - 3);
            a.set(0, x.clone());
            b.set(0, x);
            a.sim.step();
            b.sim.step();
            assert_eq!(a.get(1), b.get(1), "tick {tick}: {src}");
        }
    }
}

#[test]
fn constant_evaluation_preserves_checks_globals_and_waits() {
    let globals = "output y: int @ Y\ng = 0\ndef f(n):\n    global g\n    g += n\n    return g\nwhile True:\n    y = f(2)\n    wait 1\ntest \"effect\":\n    run 50 ticks\n    assert y > 2\n";
    build(globals, Opt::Size, true);
    let checked = format!("{PORTS}def f(n):\n    a = 3 // n\n    return a\nwhile True:\n    y = x + f(0)\n    wait 1\ntest \"check\":\n    run 50 ticks\n    assert error != 0\n    assert y == 0\n");
    build(&checked, Opt::Size, true);
    let waiting = format!("{PORTS}def f(n):\n    wait 20\n    return n\nwhile True:\n    y = x + f(3)\n    wait 1\ntest \"wait\":\n    run 10 ticks\n    assert y == 0\n    run 50 ticks\n    assert y == 3\n");
    build(&waiting, Opt::Size, false);
    // Budget exhaustion must fall back to runtime compilation, not reject or hang.
    let divergent = format!("{PORTS}def f(n):\n    while n:\n        n += 0\n    return n\nwhile True:\n    y = x + f(1)\n");
    build(&divergent, Opt::Size, false);
}

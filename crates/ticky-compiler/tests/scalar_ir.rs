//! Scalar simplification must preserve wrapping values and streaming input alignment.
use ticky_compiler::{compile, Options};
use ticky_compiler::testrun::{Harness, PVal};
use ticky_factorio::netlist::Kind;

fn source(expression: &str, cadence: &str) -> String {
    format!("input x: int @ X\ninput y: int @ Y\noutput z: int @ Z\nevery {cadence}:\n    z = {expression}\n")
}

#[test]
fn scalar_combinator_counts() {
    for cadence in ["tick"] {
        for (original, reduced) in [
            ("(x*y)-(y*x)", "0"),
            ("(x*3)*5", "x*15"),
            ("(x+7)-7", "x"),
            ("(x^123)^123", "x"),
            ("(x&255)&15", "x&15"),
            ("(x+1)==0", "x==-1"),
            ("(x-1)!=2147483647", "x!=-2147483648"),
            ("((x<<8)&255)==0", "1"),
            ("(x<<8)&-256", "x<<8"),
            ("(x|256)|256", "x|256"),
        ] {
            let count = |expr| {
                let c = compile(&source(expr, cadence), &Options::default()).unwrap();
                c.cg.netlist.entities.iter().filter(|e| matches!(e.kind, Kind::Arith(_) | Kind::Decider(_) | Kind::Selector(_) | Kind::Constant(_))).count()
            };
            assert_eq!(count(original), count(reduced), "{cadence}: {original}");
        }
    }
}

#[test]
fn scalar_streaming_wrapping_semantics() {
    let cases: &[(&str, fn(i32, i32) -> i32)] = &[
        ("(x*y)-(y*x)+y", |_, y| y),
        ("(x*3)*5+y", |x,y| x.wrapping_mul(15).wrapping_add(y)),
        ("(x+7)-7+y", |x,y| x.wrapping_add(y)),
        ("(x+1)==0", |x,_| (x.wrapping_add(1)==0) as i32),
        ("(x-1)==2147483647", |x,_| (x.wrapping_sub(1)==i32::MAX) as i32),
        ("(x+1)<0", |x,_| (x.wrapping_add(1)<0) as i32),
        ("((x<<8)&255)+y", |_,y| y),
        ("((x>>33)&255)+y", |x,y| ((x>>1)&255).wrapping_add(y)),
        ("((x|256) if y else (x|768))&256", |_,_| 256),
    ];
    let values = [i32::MIN, i32::MAX, -1, 0, 1, 123456789, -1987654321];
    let input = |t: usize| (values[t%values.len()], values[(t*3+2)%values.len()]);
    for checks in [false, true] {
        for &(expr, expected) in cases {
            let c = compile(&source(expr, "tick"), &Options { checks, ..Default::default() }).unwrap();
            let mut h = Harness::new(&c);
            let port = |n| c.program.port_index(n).unwrap();
            let actual: Vec<_> = (0..140).map(|t| {
                let (x,y) = input(t);
                h.set(port("x"), PVal::Int(x));
                h.set(port("y"), PVal::Int(y));
                h.sim.step();
                h.get(port("z"))
            }).collect();
            assert!((0..20).any(|latency| (40..140).all(|t| {
                let (x,y)=input(t-latency);
                actual[t] == PVal::Int(expected(x,y))
            })), "streaming mismatch: {expr}, checks={checks}");
        }
    }
}

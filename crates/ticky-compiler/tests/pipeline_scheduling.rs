use ticky_compiler::{codegen, compile, program, Options};

#[test]
fn mixed_schedule_saves_a_combinator_and_preserves_iteration_alignment() {
    let src = r#"input x: int @ X
input y: int @ Y
input z: int @ Z
output a: int @ A
output b: int @ B
every tick:
    p = 4 if z else x
    a = p ^ 9
    b = p & (abs(1 if z else y) * (32 >= max(30, y)))
"#;
    let opts = Options::default();
    let c = compile(src, &opts).unwrap();
    let module = ticky_syntax::parse(src).unwrap();
    let mut endpoints = program::analyze(&module, true).unwrap();
    assert!(endpoints.blocks[0].pipe.as_ref().unwrap().taus.len() > 2);
    endpoints.blocks[0].pipe.as_mut().unwrap().taus.truncate(2);
    let old = codegen::codegen(&endpoints, false, false).unwrap();
    let count = |net: &ticky_factorio::Netlist| net.entities.iter().filter(|e| e.kind.is_combinator()).count();
    assert!(count(&c.cg.netlist) < count(&old.netlist));
    assert_eq!(c.cg.blocks[0].latency, old.blocks[0].latency);
    use ticky_compiler::testrun::{Harness, PVal};
    let mut h = Harness::new(&c);
    let port = |name| c.program.port_index(name).unwrap();
    let mut want = Vec::new();
    let mut got = Vec::new();
    for tick in 0i32..120 {
        let (x, y, z) = (tick * 7 - 120, tick * 13 % 83 - 41, tick % 3 - 1);
        for (name, value) in [("x", x), ("y", y), ("z", z)] {
            h.set(port(name), PVal::Int(value));
        }
        let p = if z != 0 { 4 } else { x };
        want.push([p ^ 9, p & ((if z != 0 { 1 } else { y }).abs() * (y <= 32) as i32)]);
        h.sim.step();
        let read = |name| match h.get(port(name)) {
            PVal::Int(v) => v,
            _ => unreachable!(),
        };
        got.push([read("a"), read("b")]);
    }
    assert!((0..20).any(|lag| (30..120).all(|t| got[t] == want[t - lag])), "outputs must use the same input iteration");
    assert!(c.cg.netlist.validate(true).is_empty());
}

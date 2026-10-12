use ticky_compiler::{compile, Compiled, Opt, Options};
use ticky_compiler::testrun::{Harness, PVal};

fn build(src: &str, checks: bool) -> Compiled {
    compile(src, &Options { checks, poles: false, ..Default::default() }).unwrap()
}
fn value(h: &Harness<'_>, name: &str) -> i32 {
    let PVal::Int(v) = h.get(h.c.program.port_index(name).unwrap()) else { panic!() };
    v
}
fn set(h: &mut Harness<'_>, name: &str, v: i32) {
    h.set(h.c.program.port_index(name).unwrap(), PVal::Int(v));
}
fn count(c: &Compiled) -> usize {
    c.cg.netlist.entities.iter().filter(|e| e.kind.is_combinator()).count()
}

#[test]
fn size_mode_can_keep_an_expensive_shared_tail() {
    let src = "input choose: bool\ninput a: int\ninput b: int\noutput x: int\noutput result: int\nif choose:\n    wait 5\n    x = a\nelse:\n    wait 7\n    x = b\nresult = (((x * 73) ^ (x >> 3)) * 91) ^ ((x * 127) >> 7)\n";
    let speed = build(src, false);
    let size = compile(src, &Options { opt: Opt::Size, poles: false, ..Default::default() }).unwrap();
    eprintln!("shared-tail candidate: speed={}, size={}", count(&speed), count(&size));
    assert!(count(&size) < count(&speed), "size {} speed {}", count(&size), count(&speed));
    for c in [&speed, &size] {
        for choose in [0, 1] {
            let mut h = Harness::new(c);
            set(&mut h, "choose", choose); set(&mut h, "a", 123); set(&mut h, "b", 456);
            for _ in 0..100 { h.sim.step(); }
            let x = if choose == 1 { 123 } else { 456 };
            assert_eq!(value(&h, "x"), x);
            assert_eq!(value(&h, "result"), (((x * 73) ^ (x >> 3)) * 91) ^ ((x * 127) >> 7));
        }
    }
}

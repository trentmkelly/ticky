use ticky_compiler::{compile, Compiled, Options};
use ticky_compiler::testrun::{Harness, PVal};

fn count(c: &Compiled) -> usize {
    c.cg.netlist.entities.iter().filter(|e| e.kind.is_combinator()).count()
}

#[test]
fn uniform_background_paint_matches_pixels() {
    let source = |uneven: bool| format!("import display\ninput x: int @ X\ninput colour: int @ C\noutput s: display.Screen(8, 4)\nevery tick:\n    s.fill(0x202020)\n{}    s.rect(x, 0, 3, 3, colour)\n", if uneven { "    s[7, 3] = 0x202021\n" } else { "" });
    let uniform = compile(&source(false), &Options::default()).unwrap();
    let uneven = compile(&source(true), &Options::default()).unwrap();
    assert_eq!(count(&uneven) - count(&uniform), 1);
    let mut h = Harness::new(&uniform);
    for (x, colour) in [(-2, 0), (0, 0x202020), (3, 0xFF8800), (7, -1), (9, i32::MIN)] {
        h.set(0, PVal::Int(x));
        h.set(1, PVal::Int(colour));
        for _ in 0..40 { h.sim.step(); }
        for k in 0..32 {
            let expected = if k / 8 < 3 && (x..x + 3).contains(&(k % 8)) { colour } else { 0x202020 };
            assert_eq!(h.pixel(0, k as usize), expected, "x={x}, pixel={k}");
        }
    }
}

#[test]
fn uniform_background_keeps_coordinates_and_colour_in_one_iteration() {
    let src = "import display\ninput x: int @ X\ninput colour: int @ C\noutput s: display.Screen(8, 4)\nevery tick:\n    s.fill(0x202020)\n    s.rect(x, 0, 3, 3, colour)\n";
    let c = compile(src, &Options::default()).unwrap();
    let lag = c.cg.blocks[0].latency.unwrap() as usize - 1;
    let mut h = Harness::new(&c);
    let mut inputs = Vec::new();
    for tick in 0..100usize {
        let x = (tick % 12) as i32 - 2;
        let colour = 100 + tick as i32;
        inputs.push((x, colour));
        h.set(0, PVal::Int(x));
        h.set(1, PVal::Int(colour));
        h.sim.step();
        if tick < 30 { continue; }
        let (x, colour) = inputs[tick - lag];
        for k in 0..32i32 {
            let expected = if k / 8 < 3 && (x..x + 3).contains(&(k % 8)) { colour } else { 0x202020 };
            assert_eq!(h.pixel(0, k as usize), expected, "tick {tick}, pixel {k}, lag {lag}");
        }
    }
}

use ticky_compiler::{compile, Options};
use ticky_compiler::testrun::{Harness, PVal};

// Fully redrawn peripherals still need their holds: short RUN interruptions can leave
// delayed enable bubbles while RUN is high. These traces protect the observable value
// during those bubbles for both the delay-chain and saturating-counter warmup schemes.
#[test]
fn delayed_run_bubble_keeps_the_last_redraw() {
    let src = "import display\ninput x: int @ X\noutput s: display.Screen(4, 2)\nevery tick:\n    s.fill(x)\n";
    let c = compile(src, &Options::default()).unwrap();
    let mut h = Harness::new(&c);
    for tick in 0..17 {
        h.sim.set_constant_on(c.cg.run_switch, !matches!(tick, 0 | 12));
        h.set(0, PVal::Int(tick * 7 - 200));
        h.sim.step();
    }
    assert_eq!(h.pixel(0, 0), -116);
}

#[test]
fn counter_warmup_bubble_keeps_the_last_redraw() {
    let src = "import display\ninput x: int @ X\noutput s: display.Screen(4, 2)\nevery tick:\n    s.fill(x * 3 + 1)\n";
    let c = compile(src, &Options::default()).unwrap();
    let mut h = Harness::new(&c);
    let mut random = 0x4198_abcdu32;
    for tick in 0..255 {
        random = random.wrapping_mul(1664525).wrapping_add(1013904223);
        let on = if tick < 120 { !matches!(tick, 0 | 12 | 21..=23 | 36 | 38 | 40 | 70..=80) } else { random % 10 > 1 };
        h.sim.set_constant_on(c.cg.run_switch, on);
        h.set(0, PVal::Int(tick * 7 - 200));
        h.sim.step();
    }
    assert_eq!(h.pixel(0, 0), 4609);
}

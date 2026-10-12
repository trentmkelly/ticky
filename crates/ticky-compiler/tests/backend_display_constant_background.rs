use ticky_compiler::display::glyph;
use ticky_compiler::testrun::{Harness, PVal};
use ticky_compiler::{compile, Opt, Options};

const SOURCE: &str = include_str!("../../../examples/segment-monitor.ticky");

fn reference(n: i32) -> Vec<i32> {
    let mut pixels = vec![0; 90];
    let mut draw = |text: &str, colour| {
        for (i, ch) in text.chars().enumerate() {
            let bits = if ch == '#' { 0x7fff } else { glyph(ch).unwrap() };
            for k in 0..15 {
                if bits >> k & 1 != 0 {
                    pixels[k / 3 * 15 + i * 4 + k % 3] = colour;
                }
            }
        }
    };
    draw("8888", 0x181818);
    let n = n.clamp(-99999, 99999);
    let text = n.to_string();
    let text = if text.len() > 4 {
        let digits = n.unsigned_abs().to_string();
        format!("#{}", &digits[digits.len() - 3..])
    } else {
        format!("{text:>4}")
    };
    draw(&text, 0x40ff40);
    pixels[75..].fill(0x204060);
    pixels
}

fn pixels(h: &Harness) -> Vec<i32> {
    (0..90).map(|k| h.pixel(0, k)).collect()
}

#[test]
fn segmented_monitor_pixels_changing_values_and_restart() {
    for opt in [Opt::Speed, Opt::Size] {
        for checks in [false, true] {
            let c = compile(SOURCE, &Options { opt, checks, ..Default::default() }).unwrap();
            assert!(c.cg.netlist.validate(true).is_empty());
            // Frozen baseline: 37/33 without checks, 39/35 with checks.
            let limit = (if opt == Opt::Speed { 36 } else { 32 }) + if checks { 2 } else { 0 };
            assert!(c.cg.netlist.entities.iter().filter(|e| e.kind.is_combinator()).count() <= limit);
            let mut h = Harness::new(&c);
            for n in [0, 1, 42, 123, -42, -999, 9999, 10000, -1000, i32::MIN, i32::MAX] {
                h.set(0, PVal::Int(n));
                for _ in 0..100 {
                    h.sim.step();
                }
                assert_eq!(pixels(&h), reference(n), "{opt:?}, checks={checks}, n={n}");
            }
            // Long and short RUN interruptions, then a fresh changing stream. Holds and
            // reset logic must still produce complete frames after each restart.
            for duration in [1, 3, 40] {
                h.sim.set_constant_on(c.cg.run_switch, false);
                for _ in 0..duration {
                    h.sim.step();
                }
                h.sim.set_constant_on(c.cg.run_switch, true);
                h.set(0, PVal::Int(-73));
                for _ in 0..100 {
                    h.sim.step();
                }
                assert_eq!(pixels(&h), reference(-73));
            }
            if opt == Opt::Speed {
                let lag = c.cg.blocks[0].latency.unwrap() as usize - 1;
                let mut history = Vec::new();
                for tick in 0..100 {
                    let n = tick as i32 * 37 - 999;
                    history.push(n);
                    h.set(0, PVal::Int(n));
                    h.sim.step();
                    if tick >= 30 {
                        assert_eq!(pixels(&h), reference(history[tick - lag]));
                    }
                }
            }
        }
    }
}

#[test]
fn constant_background_checked_halt_and_restart() {
    let source = SOURCE.replace("    face.number", "    assert reading != 13\n    face.number");
    for opt in [Opt::Speed, Opt::Size] {
        let c = compile(&source, &Options { opt, checks: true, ..Default::default() }).unwrap();
        let mut h = Harness::new(&c);
        h.set(0, PVal::Int(42));
        for _ in 0..100 {
            h.sim.step();
        }
        assert_eq!(pixels(&h), reference(42));
        h.set(0, PVal::Int(13));
        for _ in 0..100 {
            h.sim.step();
        }
        assert_ne!(h.get(c.program.error_port.unwrap()), PVal::Int(0));
        let halted = pixels(&h);
        for _ in 0..100 {
            h.sim.step();
        }
        assert_eq!(pixels(&h), halted);
        h.sim.set_constant_on(c.cg.run_switch, false);
        h.set(0, PVal::Int(-73));
        for _ in 0..40 {
            h.sim.step();
        }
        h.sim.set_constant_on(c.cg.run_switch, true);
        for _ in 0..100 {
            h.sim.step();
        }
        assert_eq!(h.get(c.program.error_port.unwrap()), PVal::Int(0));
        assert_eq!(pixels(&h), reference(-73));
    }
}

#[test]
fn sparse_background_delta_handles_zero_equal_and_wrapping_colours() {
    for colour in [0i32, 17, -1, i32::MIN, i32::MAX] {
        let source = format!("import display\ninput x: int @ X\noutput s: display.Screen(8, 4)\nevery tick:\n    s.fill(0)\n    s[1, 1] = 17\n    s[5, 2] = -2147483648\n    s.rect(x, 0, 3, 4, {colour})\n");
        for opt in [Opt::Speed, Opt::Size] {
            for checks in [false, true] {
                let c = compile(&source, &Options { opt, checks, ..Default::default() }).unwrap();
                let mut h = Harness::new(&c);
                for x in [-4, -1, 0, 3, 6, 10] {
                    h.set(0, PVal::Int(x));
                    for _ in 0..60 {
                        h.sim.step();
                    }
                    for k in 0..32 {
                        let old = match k {
                            9 => 17,
                            21 => i32::MIN,
                            _ => 0,
                        };
                        let expected = if (x..x + 3).contains(&(k % 8)) { colour } else { old };
                        assert_eq!(h.pixel(0, k as usize), expected, "colour={colour}, x={x}, pixel={k}");
                    }
                }
            }
        }
    }
}

#[test]
fn conditional_text_clips_across_banks() {
    let source = "import display\ninput x: int @ X\ninput y: int @ Y\ninput visible: bool @ V\noutput s: display.Screen(40, 30)\nevery tick:\n    s.fill(0)\n    s[1, 1] = 17\n    s[0, 29] = 23\n    if visible:\n        s.text(x, y, \"OK\", 0x123456)\n";
    for opt in [Opt::Speed, Opt::Size] {
        for checks in [false, true] {
            let c = compile(source, &Options { opt, checks, ..Default::default() }).unwrap();
            let mut h = Harness::new(&c);
            for (x, y, visible) in [(-2, 0, 1), (38, 27, 1), (0, 26, 1), (0, 26, 0), (10, -2, 1)] {
                h.set(0, PVal::Int(x));
                h.set(1, PVal::Int(y));
                h.set(2, PVal::Int(visible));
                for _ in 0..100 {
                    h.sim.step();
                }
                let mut expected = vec![0; 1200];
                expected[41] = 17;
                expected[1160] = 23;
                if visible != 0 {
                    for (i, ch) in "OK".chars().enumerate() {
                        let bits = glyph(ch).unwrap();
                        for k in 0..15 {
                            let (px, py) = (x + i as i32 * 4 + k % 3, y + k / 3);
                            if bits >> k & 1 != 0 && (0..40).contains(&px) && (0..30).contains(&py) {
                                expected[(py * 40 + px) as usize] = 0x123456;
                            }
                        }
                    }
                }
                for (k, value) in expected.iter().enumerate() {
                    assert_eq!(h.pixel(0, k), *value, "{opt:?}, checks={checks}, ({x}, {y}), visible={visible}, pixel={k}");
                }
            }
        }
    }
}

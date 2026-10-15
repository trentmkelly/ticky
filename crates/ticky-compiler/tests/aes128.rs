//! End-to-end AES circuits against FIPS 197 C.1 and independent OpenSSL answers.
//! Fixture blocks: FIPS input, zero, all ones, boundary bits, ascending bytes, and
//! ten random blocks (Python random.Random(197).randbytes(16)); keys: ascending,
//! zero and all ones. tools/verify-aes-vectors.py rechecks the expected answers.
use ticky_compiler::{compile, testrun::{run_tests, Harness, PVal}, Opt, Options};

const SOURCE: &str = include_str!("../../../examples/aes128.ticky");

fn words(hex: &str) -> [i32; 4] {
    assert_eq!(hex.len(), 32);
    std::array::from_fn(|i| u32::from_str_radix(&hex[i * 8..i * 8 + 8], 16).unwrap() as i32)
}
fn set(h: &mut Harness<'_>, name: &str, value: i32) {
    h.set(h.c.program.port_index(name).unwrap(), PVal::Int(value));
}
fn get(h: &Harness<'_>, name: &str) -> i32 {
    match h.get(h.c.program.port_index(name).unwrap()) {
        PVal::Int(n) => n,
        _ => panic!("expected integer port {name}"),
    }
}
fn await_port(h: &mut Harness<'_>, name: &str, value: i32, limit: usize) {
    for _ in 0..limit {
        if get(h, name) == value { return; }
        h.sim.step();
    }
    panic!("timed out waiting for {name}={value}");
}
fn input(h: &mut Harness<'_>, data: [i32; 4]) {
    for (name, value) in ["p0", "p1", "p2", "p3"].into_iter().zip(data) { set(h, name, value); }
}
fn output(h: &Harness<'_>) -> [i32; 4] {
    ["c0", "c1", "c2", "c3"].map(|name| get(h, name))
}

#[test]
fn aes_known_answers_repeated_requests_and_input_sampling() {
    let fixtures: serde_json::Value = serde_json::from_str(include_str!("fixtures/aes128-vectors.json")).unwrap();
    let key_line = SOURCE.lines().find(|line| line.starts_with("KEY = ")).unwrap();
    for case in fixtures.as_array().unwrap() {
        let key = case["key"].as_str().unwrap();
        let src = SOURCE.replace(key_line, &format!("KEY = {:?}", words(key)));
        for opt in [Opt::Speed, Opt::Size] {
            for checks in [false, true] {
                let c = compile(&src, &Options { opt, checks, ..Default::default() })
                    .unwrap_or_else(|ds| panic!("{}", ds.iter().map(|d| d.render("aes", &src)).collect::<String>()));
                assert!(c.cg.netlist.validate(true).is_empty());
                let mut h = Harness::new(&c);
                for vector in case["vectors"].as_array().unwrap() {
                    await_port(&mut h, "ready", 1, 100);
                    assert_eq!(get(&h, "done"), 0);
                    let previous = output(&h);
                    input(&mut h, words(vector["plaintext"].as_str().unwrap()));
                    set(&mut h, "start", 1);
                    await_port(&mut h, "ready", 0, 100);
                    // Once accepted, changing every input must not alter this block.
                    input(&mut h, [i32::MIN, i32::MAX, -1, 0]);
                    for _ in 0..2000 {
                        if get(&h, "done") != 0 { break; }
                        assert_eq!(output(&h), previous, "partial ciphertext became visible");
                        h.sim.step();
                    }
                    assert_eq!(get(&h, "done"), 1, "encryption timed out");
                    let expected = words(vector["ciphertext"].as_str().unwrap());
                    assert_eq!(output(&h), expected, "key={key}, {opt:?}, checks={checks}, {vector}");
                    assert_eq!(get(&h, "ready"), 0);
                    // A held request must not start another encryption.
                    for _ in 0..350 { h.sim.step(); }
                    assert_eq!(output(&h), expected);
                    assert_eq!(get(&h, "done"), 1);
                    if checks { assert_eq!(get(&h, "error"), 0); }
                    set(&mut h, "start", 0);
                }
            }
        }
    }
}

#[test]
fn aes_example_and_run_restart() {
    for opt in [Opt::Speed, Opt::Size] {
        for checks in [false, true] {
            let c = compile(SOURCE, &Options { opt, checks, ..Default::default() }).unwrap();
            for r in run_tests(&c, SOURCE) { assert!(r.failure.is_none(), "{}: {:?}", r.name, r.failure); }
            let mut h = Harness::new(&c);
            await_port(&mut h, "ready", 1, 100);
            input(&mut h, [1, 2, 3, 4]);
            set(&mut h, "start", 1);
            await_port(&mut h, "ready", 0, 100);
            for _ in 0..40 { h.sim.step(); }
            assert_eq!(get(&h, "done"), 0);
            h.sim.set_constant_on(c.cg.run_switch, false);
            set(&mut h, "start", 0);
            for _ in 0..40 { h.sim.step(); }
            h.sim.set_constant_on(c.cg.run_switch, true);
            await_port(&mut h, "ready", 1, 100);
            assert_eq!(get(&h, "done"), 0);
            input(&mut h, words("00112233445566778899aabbccddeeff"));
            set(&mut h, "start", 1);
            await_port(&mut h, "done", 1, 2000);
            assert_eq!(output(&h), words("69c4e0d86a7b0430d8cdb78070b4c55a"));
            if checks { assert_eq!(get(&h, "error"), 0); }
        }
    }
}

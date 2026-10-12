use ticky_compiler::{compile, testrun::run_tests, Opt, Options};

#[test]
fn nested_flag_filters_preserve_sparse_domains_and_shared_consumers() {
    let mut seed = 0x5147_u32;
    for flag in [0i32, 3, -7, i32::MIN] {
        let mut src = format!(r#"input stock: Bundle
input cutoff: int @ C
output flags: Bundle
output selected: Bundle
output recolored: Bundle
output weight: int @ W
output kinds: int @ K
every tick:
    flags = {{s: {flag} for s, v in stock.items() if v < 10 or v > 100}}
    selected = {{s: v for s, v in flags.items() if v >= cutoff or v == -7}}
    recolored = {{s: -2 for s, v in flags.items() if v != 3 and v < 0}}
    weight = selected.total()
    kinds = len(selected)
test "random and signed boundary values":
"#);
        for i in 0..24 {
            let values: Vec<i32> = (0..4).map(|j| {
                seed = seed.wrapping_mul(1664525).wrapping_add(1013904223);
                match (i + j) % 9 { 0 => 0, 1 => i32::MIN, 2 => i32::MAX, _ => (seed as i32) % 150 }
            }).collect();
            let cutoff = [i32::MIN, -7, 0, 3, 4, i32::MAX][i % 6];
            let names = ["coal", "stone", "signal-C", "iron-plate"];
            let bundle = |predicate: &dyn Fn(i32) -> bool, value: &dyn Fn(i32) -> i32| {
                let entries: Vec<_> = values.iter().zip(names).filter(|(v, _)| **v != 0 && predicate(**v)).map(|(v, s)| format!("\"{s}\": {}", value(*v))).collect();
                format!("{{{}}}", entries.join(", "))
            };
            let present = |v: i32| flag != 0 && (v < 10 || v > 100);
            let selected = |v: i32| present(v) && (flag >= cutoff || flag == -7);
            let n = values.iter().filter(|v| **v != 0 && selected(**v)).count() as i32;
            src.push_str(&format!("    set stock = {}\n    set cutoff = {cutoff}\n    run 40 ticks\n    assert flags == {}\n    assert selected == {}\n    assert recolored == {}\n    assert kinds == {n} and weight == {}\n", bundle(&|_| true, &|v| v), bundle(&present, &|_| flag), bundle(&selected, &|_| flag), bundle(&|v| present(v) && flag != 3 && flag < 0, &|_| -2), n.wrapping_mul(flag)));
        }
        for periodic in [false, true] {
            let src = if periodic { src.replace("every tick:", "every 60 ticks:").replace("run 40 ticks", "run 180 ticks") } else { src.clone() };
            for opt in [Opt::Speed, Opt::Size] {
                for checks in [false, true] {
                    let c = compile(&src, &Options { opt, checks, ..Default::default() }).unwrap_or_else(|d| panic!("{}", d[0].render("flags", &src)));
                    assert!(c.cg.netlist.validate(true).is_empty());
                    for r in run_tests(&c, &src) {
                        assert!(r.failure.is_none(), "{}", r.failure.map(|d| d.render("flags", &src)).unwrap_or_default());
                    }
                }
            }
        }
    }
}

#[test]
fn constant_flag_predicate_fuses_into_original_filter() {
    let src = "input stock: Bundle\noutput selected: Bundle\nevery tick:\n    flags = {s: 3 for s, v in stock.items() if v < 10}\n    selected = {s: v for s, v in flags.items() if v >= 2}\n";
    let c = compile(src, &Options::default()).unwrap();
    let filters = c.cg.netlist.entities.iter().filter(|e| e.description.as_deref().is_some_and(|s| s.ends_with(": filter"))).count();
    assert_eq!(filters, 1);
}

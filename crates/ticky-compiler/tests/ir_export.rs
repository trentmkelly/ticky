//! `TICKY_EXPORT_IR` (ir_export.rs) writes what `tools/validate.py` needs: the probe table,
//! each unit's graph, rewrite claims (with path conditions for `//`) and writers before and
//! after fusion. One test only: the variable is read once per process.
use ticky_compiler::{compile, Options};

const SRC: &str = "input x: int @ X
input y: int @ Y
output z: int @ Z
output w: int @ W
output v: int @ V
every tick:
    if x > 0:
        z = (x * 4) // 8
    w = max(y, 3) // 7 + (x + 1) - 1

while True:
    wait until x > 5
    v = y % 6
    wait 3
";

#[test]
fn export_writes_units_claims_and_writers() {
    let path = std::env::temp_dir().join(format!("ticky-ir-export-{}.jsonl", std::process::id()));
    let _ = std::fs::remove_file(&path);
    std::env::set_var("TICKY_EXPORT_IR", &path);
    let with = compile(SRC, &Options::default()).expect("compiles");
    let text = std::fs::read_to_string(&path).expect("export written");
    let _ = std::fs::remove_file(&path);
    let lines: Vec<serde_json::Value> = text.lines().map(|l| serde_json::from_str(l).expect("JSON line")).collect();

    let probe = &lines[0]["probe"];
    assert!(probe["ops"].as_array().unwrap().len() > 1000, "operator table");
    let units: Vec<&serde_json::Value> = lines.iter().filter(|l| l.get("unit").is_some()).collect();
    let names: Vec<&str> = units.iter().map(|u| u["unit"].as_str().unwrap()).collect();
    assert!(names.contains(&"every block 0") && names.contains(&"main"), "{names:?}");

    for u in &units {
        let n = u["nodes"].as_array().unwrap().len() as u64;
        for c in u["claims"].as_array().unwrap() {
            assert!(c["res"].as_u64().unwrap() < n, "claim result is a node");
        }
    }
    let block = units.iter().find(|u| u["unit"] == "every block 0").unwrap();
    let claims = block["claims"].as_array().unwrap();
    // `(x * 4) // 8` under `x > 0` is a floor division with that path condition.
    assert!(claims.iter().any(|c| c["rule"] == "floor_div" && !c["path"].as_array().unwrap().is_empty()), "{claims:?}");
    let writer = &block["writers"][0];
    assert_eq!(writer["writes"].as_array().unwrap().len(), 2);
    assert_eq!(writer["plans"].as_array().unwrap().len(), 2);
    assert!(block["srcs"].as_array().unwrap().iter().any(|s| s["kind"] == "Input" && s["name"] == "x"));

    let main = units.iter().find(|u| u["unit"] == "main").unwrap();
    let writers = main["writers"].as_array().unwrap();
    assert!(writers.iter().any(|w| !w["conds"].as_array().unwrap().is_empty()), "wait condition before/after fusion");
    assert!(!with.cg.netlist.entities.is_empty());
}

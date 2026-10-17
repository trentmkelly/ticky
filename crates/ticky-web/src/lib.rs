//! Ticky in the browser (`web/`): the compiler and the test runner behind two functions that
//! take source and options and return JSON, for wasm-bindgen.
//!
//! Options (JSON, all optional): `opt` (`"speed"` or `"size"`), `place` (`"grid"` or
//! `"anneal"`), `poles` (bool), `checks` (bool), `effort` (number).

use serde_json::{json, Value};
use ticky_compiler::testrun::run_tests;
use ticky_compiler::{compile as compile_src, Compiled, Opt, Options};
use ticky_factorio::netlist::{Dir, Kind, Selector};
use ticky_factorio::{ArOp, CmpOp, Conn};
use ticky_syntax::diag::Severity;
use ticky_syntax::Diag;
use wasm_bindgen::prelude::wasm_bindgen;

thread_local! {
    static PANIC: std::cell::RefCell<Option<String>> = const { std::cell::RefCell::new(None) };
}

/// Keeps a compiler panic's message for [`last_panic`] (a panic aborts the wasm instance, and
/// the page only sees "unreachable").
#[wasm_bindgen(start)]
pub fn start() {
    std::panic::set_hook(Box::new(|info| {
        PANIC.with(|p| *p.borrow_mut() = Some(info.to_string()));
    }));
}

/// The message of the panic that stopped the compiler, if any.
#[wasm_bindgen]
pub fn last_panic() -> Option<String> {
    PANIC.with(|p| p.borrow().clone())
}

fn options(json: &str) -> Options {
    let o: Value = serde_json::from_str(json).unwrap_or(Value::Null);
    let opt = if o["opt"] == "size" { Opt::Size } else { Opt::Speed };
    let anneal = (o["place"] == "anneal").then(|| ticky_compiler::place::AnnealOpts {
        effort: o["effort"].as_f64().unwrap_or(1.0).clamp(0.05, 10.0),
        ..Default::default()
    });
    Options {
        opt,
        poles: o["poles"].as_bool().unwrap_or(true),
        checks: o["checks"].as_bool().unwrap_or(false),
        anneal,
        label: "Ticky".into(),
        ..Default::default()
    }
}

/// UTF-16 offset of byte offset `b` in `src` (what the editor counts in).
fn utf16(src: &str, b: usize) -> usize {
    let mut b = b.min(src.len());
    while !src.is_char_boundary(b) {
        b -= 1;
    }
    src[..b].encode_utf16().count()
}

fn diag(d: &Diag, src: &str) -> Value {
    let severity = match d.severity {
        Severity::Error => "error",
        Severity::Warning => "warning",
        Severity::Note => "info",
    };
    let from = utf16(src, d.span.start);
    let to = utf16(src, d.span.end).max(from);
    json!({
        "severity": severity,
        "message": d.message,
        "help": d.help,
        "from": from,
        "to": to,
        "rendered": d.render("program.ticky", src),
    })
}

/// What a combinator's display shows (the game's `*_symbol_sprites` names, without the suffix).
fn symbol(k: &Kind) -> Option<&'static str> {
    Some(match k {
        Kind::Arith(a) => match a.op {
            ArOp::Add => "plus",
            ArOp::Sub => "minus",
            ArOp::Mul => "multiply",
            ArOp::Div => "divide",
            ArOp::Mod => "modulo",
            ArOp::Pow => "power",
            ArOp::Shl => "left_shift",
            ArOp::Shr => "right_shift",
            ArOp::And => "and",
            ArOp::Or => "or",
            ArOp::Xor => "xor",
        },
        Kind::Decider(d) => match d.conds.first()?.cmp {
            CmpOp::Gt => "greater",
            CmpOp::Lt => "less",
            CmpOp::Eq => "equal",
            CmpOp::Ne => "not_equal",
            CmpOp::Le => "less_or_equal",
            CmpOp::Ge => "greater_or_equal",
        },
        Kind::Selector(s) => match s {
            Selector::Select { max: true, .. } | Selector::SelectAt { max: true, .. } => "max",
            Selector::Select { .. } | Selector::SelectAt { .. } => "min",
            Selector::Count { .. } => "count",
            Selector::Random { .. } => "random",
            Selector::StackSize => "stack_size",
            Selector::RocketCapacity => "rocket_capacity",
            Selector::QualityFilter { .. } | Selector::QualitySet { .. } => "quality",
        },
        _ => return None,
    })
}

/// Which of a combinator's terminals a wire end uses: `"in"`, `"out"`, or `""` (one terminal).
fn side(c: Conn) -> &'static str {
    match c {
        Conn::InRed | Conn::InGreen => "in",
        Conn::OutRed | Conn::OutGreen => "out",
        _ => "",
    }
}

/// The placed circuit, for drawing: entities (centre, size, kind, what made them) and wires
/// between their centres.
fn circuit(c: &Compiled) -> Value {
    let net = &c.cg.netlist;
    let entities: Vec<Value> = (0..net.entities.len())
        .map(|i| {
            let e = &net.entities[i];
            let (w, h) = net.footprint(i);
            let dir = match e.dir {
                Dir::North => 0,
                Dir::East => 1,
                Dir::South => 2,
                Dir::West => 3,
            };
            json!({
                "name": e.kind.proto_name(),
                "x": e.pos.0, "y": e.pos.1, "w": w, "h": h, "dir": dir,
                "symbol": symbol(&e.kind),
                "description": e.description,
            })
        })
        .collect();
    let wires: Vec<Value> = net
        .wires
        .iter()
        .filter_map(|w| {
            let colour = match (w.a.1, w.b.1) {
                (Conn::Copper, _) | (_, Conn::Copper) => return None,
                (Conn::InRed | Conn::OutRed | Conn::Red, _) => "red",
                _ => "green",
            };
            Some(json!({ "a": w.a.0, "b": w.b.0, "colour": colour, "as": side(w.a.1), "bs": side(w.b.1) }))
        })
        .collect();
    json!({ "entities": entities, "wires": wires })
}

/// Compiles `src`: `{ ok, diagnostics, report?, blueprint?, stats?, circuit? }`.
#[wasm_bindgen]
pub fn compile(src: &str, opts: &str) -> String {
    let out = match compile_src(src, &options(opts)) {
        Ok(c) => {
            let combinators = c.cg.netlist.entities.iter().filter(|e| e.kind.is_combinator()).count();
            json!({
                "ok": true,
                "diagnostics": c.warnings.iter().map(|d| diag(d, src)).collect::<Vec<_>>(),
                "report": c.report(src),
                "blueprint": c.blueprint_string(),
                "stats": {
                    "combinators": combinators,
                    "entities": c.cg.netlist.entities.len(),
                    "width": c.layout.width,
                    "height": c.layout.height,
                    "poles": c.layout.poles,
                    "relays": c.layout.relays,
                },
                "circuit": circuit(&c),
            })
        }
        Err(ds) => json!({ "ok": false, "diagnostics": ds.iter().map(|d| diag(d, src)).collect::<Vec<_>>() }),
    };
    out.to_string()
}

/// Compiles `src` and runs its `test` blocks in the simulator:
/// `{ ok, diagnostics, tests: [{ name, ticks, passed, failure? }] }`.
#[wasm_bindgen]
pub fn test(src: &str, opts: &str) -> String {
    let out = match compile_src(src, &options(opts)) {
        Ok(c) => {
            let tests: Vec<Value> = run_tests(&c, src)
                .iter()
                .map(|t| {
                    json!({
                        "name": t.name,
                        "ticks": t.ticks,
                        "passed": t.failure.is_none(),
                        "failure": t.failure.as_ref().map(|d| diag(d, src)),
                    })
                })
                .collect();
            json!({ "ok": true, "diagnostics": c.warnings.iter().map(|d| diag(d, src)).collect::<Vec<_>>(), "tests": tests })
        }
        Err(ds) => json!({ "ok": false, "diagnostics": ds.iter().map(|d| diag(d, src)).collect::<Vec<_>>(), "tests": [] }),
    };
    out.to_string()
}

/// The compiler's version.
#[wasm_bindgen]
pub fn version() -> String {
    env!("CARGO_PKG_VERSION").into()
}

#[cfg(test)]
mod tests {
    use super::*;

    const SRC: &str = "input a: int @ A\noutput b: int @ B\nevery tick:\n    b = a * 2\n\ntest \"doubles\":\n    set a = 21\n    run 10 ticks\n    assert b == 42\n";

    #[test]
    fn compiles_and_tests() {
        let c: Value = serde_json::from_str(&compile(SRC, "{}")).unwrap();
        assert_eq!(c["ok"], true, "{c}");
        assert!(c["blueprint"].as_str().unwrap().starts_with('0'));
        assert!(c["stats"]["combinators"].as_u64().unwrap() >= 1);
        let es = c["circuit"]["entities"].as_array().unwrap();
        // The doubling combinator shows `*`; wires name the terminals they use.
        assert!(es.iter().any(|e| e["name"] == "arithmetic-combinator" && e["symbol"] == "multiply" && e["dir"].is_u64()), "{es:?}");
        let wires = c["circuit"]["wires"].as_array().unwrap();
        assert!(wires.iter().any(|w| w["as"] == "in" || w["bs"] == "in"), "{wires:?}");
        let t: Value = serde_json::from_str(&test(SRC, r#"{"opt":"size"}"#)).unwrap();
        assert_eq!(t["tests"][0]["passed"], true, "{t}");
    }

    #[test]
    fn errors_point_into_the_source() {
        let src = "output b: int @ B\nb = nope + 1\n";
        let c: Value = serde_json::from_str(&compile(src, "{}")).unwrap();
        assert_eq!(c["ok"], false);
        let d = &c["diagnostics"][0];
        assert_eq!(d["severity"], "error");
        assert_eq!(&src[d["from"].as_u64().unwrap() as usize..d["to"].as_u64().unwrap() as usize], "nope");
    }
}

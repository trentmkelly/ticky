//! Factorio 2.0 blueprint JSON and blueprint strings (`0` + base64(zlib(json))).

use std::io::{Read, Write};

use base64::Engine;
use serde_json::{json, Map, Value};

use crate::netlist::*;
use crate::signals::{Sig, SignalKind, SignalTable};

/// Blueprint version written by Factorio 2.0.77.
pub const VERSION: u64 = 562949958467584;

fn signal_json(t: &SignalTable, s: Sig) -> Value {
    let info = t.info(s);
    match info.kind {
        // The game omits the type for items.
        SignalKind::Item => json!({ "name": info.name }),
        k => json!({ "type": k.as_str(), "name": info.name }),
    }
}

fn nets_json(n: Nets) -> Option<Value> {
    (n != Nets::BOTH).then(|| json!({ "red": n.red, "green": n.green }))
}

fn arith_json(t: &SignalTable, a: &Arith) -> Value {
    let mut m = Map::new();
    match a.first {
        Operand::Sig(s) => {
            m.insert("first_signal".into(), signal_json(t, s));
        }
        Operand::Const(c) => {
            m.insert("first_constant".into(), json!(c));
        }
    }
    match a.second {
        Operand::Sig(s) => {
            m.insert("second_signal".into(), signal_json(t, s));
        }
        Operand::Const(c) => {
            m.insert("second_constant".into(), json!(c));
        }
    }
    m.insert("operation".into(), json!(a.op.symbol()));
    m.insert("output_signal".into(), signal_json(t, a.out));
    if let Some(n) = nets_json(a.first_nets) {
        m.insert("first_signal_networks".into(), n);
    }
    if let Some(n) = nets_json(a.second_nets) {
        m.insert("second_signal_networks".into(), n);
    }
    json!({ "arithmetic_conditions": m })
}

fn decider_json(t: &SignalTable, d: &Decider) -> Value {
    let conds: Vec<Value> = d
        .conds
        .iter()
        .enumerate()
        .map(|(i, c)| {
            let mut m = Map::new();
            m.insert("first_signal".into(), signal_json(t, c.first));
            match c.second {
                Operand::Sig(s) => {
                    m.insert("second_signal".into(), signal_json(t, s));
                }
                Operand::Const(k) => {
                    m.insert("constant".into(), json!(k));
                }
            }
            m.insert("comparator".into(), json!(c.cmp.symbol()));
            if i > 0 {
                m.insert("compare_type".into(), json!(if c.and { "and" } else { "or" }));
            }
            if let Some(n) = nets_json(c.first_nets) {
                m.insert("first_signal_networks".into(), n);
            }
            if let Some(n) = nets_json(c.second_nets) {
                m.insert("second_signal_networks".into(), n);
            }
            Value::Object(m)
        })
        .collect();
    let outs: Vec<Value> = d
        .outputs
        .iter()
        .map(|o| {
            let mut m = Map::new();
            m.insert("signal".into(), signal_json(t, o.sig));
            if !o.copy {
                m.insert("copy_count_from_input".into(), json!(false));
                m.insert("constant".into(), json!(o.constant));
            } else if let Some(n) = nets_json(o.nets) {
                m.insert("networks".into(), n);
            }
            Value::Object(m)
        })
        .collect();
    json!({ "decider_conditions": { "conditions": conds, "outputs": outs } })
}

fn selector_json(t: &SignalTable, s: &Selector) -> Value {
    match s {
        Selector::Select { max, index } => json!({ "operation": "select", "select_max": max, "index_constant": index }),
        Selector::Count { out } => json!({ "operation": "count", "count_signal": signal_json(t, *out) }),
    }
}

fn constant_json(t: &SignalTable, c: &ConstComb) -> Value {
    let filters: Vec<Value> = c
        .values
        .iter()
        .enumerate()
        .map(|(i, (s, v))| {
            let mut f = match signal_json(t, *s) {
                Value::Object(m) => m,
                _ => unreachable!(),
            };
            f.insert("index".into(), json!(i + 1));
            f.insert("quality".into(), json!("normal"));
            f.insert("comparator".into(), json!("="));
            f.insert("count".into(), json!(v));
            Value::Object(f)
        })
        .collect();
    let mut m = Map::new();
    m.insert("sections".into(), json!({ "sections": [{ "index": 1, "filters": filters }] }));
    if !c.on {
        m.insert("is_on".into(), json!(false));
    }
    Value::Object(m)
}

pub fn to_json(n: &Netlist, t: &SignalTable, icons: &[Sig]) -> Value {
    let entities: Vec<Value> = n
        .entities
        .iter()
        .enumerate()
        .map(|(i, e)| {
            let mut m = Map::new();
            m.insert("entity_number".into(), json!(i + 1));
            m.insert("name".into(), json!(e.kind.proto_name()));
            m.insert("position".into(), json!({ "x": e.pos.0, "y": e.pos.1 }));
            match e.dir {
                Dir::North => {}
                Dir::East => {
                    m.insert("direction".into(), json!(4));
                }
                Dir::West => {
                    m.insert("direction".into(), json!(12));
                }
            }
            let cb = match &e.kind {
                Kind::Arith(a) => Some(arith_json(t, a)),
                Kind::Decider(d) => Some(decider_json(t, d)),
                Kind::Selector(sel) => Some(selector_json(t, sel)),
                Kind::Constant(c) => Some(constant_json(t, c)),
                Kind::Pole => None,
            };
            if let Some(cb) = cb {
                m.insert("control_behavior".into(), cb);
            }
            if let Some(d) = &e.description {
                m.insert("player_description".into(), json!(d));
            }
            Value::Object(m)
        })
        .collect();
    let wires: Vec<Value> = n
        .wires
        .iter()
        .map(|w| json!([w.a.0 + 1, w.a.1.blueprint_id(), w.b.0 + 1, w.b.1.blueprint_id()]))
        .collect();
    let icons: Vec<Value> = icons
        .iter()
        .take(4)
        .enumerate()
        .map(|(i, s)| json!({ "signal": signal_json(t, *s), "index": i + 1 }))
        .collect();
    json!({ "blueprint": {
        "icons": icons,
        "entities": entities,
        "wires": wires,
        "item": "blueprint",
        "label": n.label,
        "description": n.description,
        "version": VERSION,
    }})
}

pub fn encode(v: &Value) -> String {
    let mut z = flate2::write::ZlibEncoder::new(Vec::new(), flate2::Compression::best());
    z.write_all(v.to_string().as_bytes()).unwrap();
    let bytes = z.finish().unwrap();
    format!("0{}", base64::engine::general_purpose::STANDARD.encode(bytes))
}

pub fn decode(s: &str) -> Result<Value, String> {
    let s = s.trim();
    let body = s.strip_prefix('0').ok_or("blueprint strings start with version byte '0'")?;
    let bytes = base64::engine::general_purpose::STANDARD.decode(body).map_err(|e| e.to_string())?;
    let mut json = String::new();
    flate2::read::ZlibDecoder::new(&bytes[..]).read_to_string(&mut json).map_err(|e| e.to_string())?;
    serde_json::from_str(&json).map_err(|e| e.to_string())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn round_trip() {
        let v = json!({ "blueprint": { "entities": [], "item": "blueprint" } });
        assert_eq!(decode(&encode(&v)).unwrap(), v);
    }
}

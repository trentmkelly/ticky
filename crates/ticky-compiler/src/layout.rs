//! Naive grid placement, power poles and wiring.
//!
//! ```text
//!   pole  RUN   core combinators in segments of 6 columns     output ports  pole
//!   |     in1   with a pole column in the middle of each      out1          |
//!   |     in2   segment                                       out2          |
//! ```
//! Wires are minimum spanning trees over each network's members, so every wire is short.

use ticky_factorio::*;

/// Combinator columns per segment; each segment also has one pole column.
const SEG: usize = 6;
/// Longest wire we allow ourselves (the game allows 9).
const MAX_WIRE: f64 = 8.5;

fn dist(a: (f64, f64), b: (f64, f64)) -> f64 {
    ((a.0 - b.0).powi(2) + (a.1 - b.1).powi(2)).sqrt()
}

/// Prim's algorithm over points; returns edges as index pairs.
fn mst(points: &[(f64, f64)]) -> Vec<(usize, usize)> {
    let n = points.len();
    if n < 2 {
        return vec![];
    }
    let mut in_tree = vec![false; n];
    let mut best = vec![(f64::INFINITY, 0usize); n];
    let mut edges = Vec::with_capacity(n - 1);
    in_tree[0] = true;
    for j in 1..n {
        best[j] = (dist(points[0], points[j]), 0);
    }
    for _ in 1..n {
        let (j, _) = (0..n)
            .filter(|j| !in_tree[*j])
            .map(|j| (j, best[j].0))
            .min_by(|a, b| a.1.partial_cmp(&b.1).unwrap().then(a.0.cmp(&b.0)))
            .unwrap();
        in_tree[j] = true;
        edges.push((best[j].1, j));
        for k in 0..n {
            if !in_tree[k] {
                let d = dist(points[j], points[k]);
                if d < best[k].0 {
                    best[k] = (d, j);
                }
            }
        }
    }
    edges
}

pub struct LayoutInfo {
    pub width: u32,
    pub height: u32,
    pub poles: usize,
}

pub fn layout(net: &mut Netlist, nets: &[crate::codegen::NetSpec]) -> Result<LayoutInfo, String> {
    let core: Vec<EntId> = (0..net.entities.len()).filter(|&i| net.entities[i].role == Role::Core).collect();
    let inputs: Vec<EntId> =
        (0..net.entities.len()).filter(|&i| matches!(net.entities[i].role, Role::InputPort { .. })).collect();
    let outputs: Vec<EntId> =
        (0..net.entities.len()).filter(|&i| matches!(net.entities[i].role, Role::OutputPort { .. })).collect();
    let run = net.find_role(|r| *r == Role::RunSwitch);

    // Roughly square: S segments of 7 columns, rows 2 tiles tall.
    let n = core.len().max(1);
    let segs = ((n as f64 / 21.0).sqrt().ceil() as usize).max(1);
    let per_row = SEG * segs;
    let rows = n.div_ceil(per_row);
    for (k, &id) in core.iter().enumerate() {
        // Serpentine, so consecutive entities (which share private wires) stay adjacent.
        let (r, j) = (k / per_row, k % per_row);
        let j = if r % 2 == 1 { per_row - 1 - j } else { j };
        let (seg, off) = (j / SEG, j % SEG);
        let col = seg * 7 + if off < 3 { off } else { off + 1 };
        // Two-tile combinators fill the slot; one-tile entities sit in its top half.
        let dy = if net.entities[id].kind.is_combinator() { 1.0 } else { 0.5 };
        net.entities[id].pos = (col as f64 + 0.5, 2.0 * r as f64 + dy);
    }
    let mut poles: Vec<(f64, f64)> = Vec::new();
    // A pole in row r powers rows r-2..=r+1.
    let mut pole_rows: Vec<usize> = (0..rows.div_ceil(4)).map(|b| (4 * b + 2).min(rows - 1)).collect();
    pole_rows.dedup();
    for &r in &pole_rows {
        for seg in 0..segs {
            poles.push(((seg * 7 + 3) as f64 + 0.5, 2.0 * r as f64 + 0.5));
        }
    }

    // Left: RUN switch above the input ports; poles one column further left.
    if let Some(r) = run {
        net.entities[r].pos = (-1.5, 0.5);
    }
    for (i, &id) in inputs.iter().enumerate() {
        net.entities[id].pos = (-2.0, i as f64 + 1.5);
    }
    let left_rows = inputs.len() + 1;
    // A pole powers 3 rows either side of its own.
    for k in 0..left_rows.div_ceil(7).max(1) {
        poles.push((-3.5, 7.0 * k as f64 + 3.5));
    }

    // Right: output ports just past the last core column.
    let w = (7 * segs) as f64;
    for (i, &id) in outputs.iter().enumerate() {
        net.entities[id].pos = (w + 1.0, i as f64 + 0.5);
    }
    if !outputs.is_empty() {
        for k in 0..outputs.len().div_ceil(7) {
            poles.push((w + 2.5, 7.0 * k as f64 + 3.5));
        }
    }

    let first_pole = net.entities.len();
    for &p in &poles {
        let id = net.add(Kind::Pole, Role::Power);
        net.entities[id].pos = p;
    }
    let pole_ids: Vec<EntId> = (first_pole..net.entities.len()).collect();
    for (a, b) in mst(&poles) {
        if dist(poles[a], poles[b]) > 9.0 {
            return Err(format!("pole gap of {:.1} tiles", dist(poles[a], poles[b])));
        }
        net.wire((pole_ids[a], Conn::Copper), (pole_ids[b], Conn::Copper));
    }

    for spec in nets {
        let points: Vec<(f64, f64)> = spec.members.iter().map(|(e, _)| net.entities[*e].pos).collect();
        for (a, b) in mst(&points) {
            if dist(points[a], points[b]) > MAX_WIRE {
                return Err(format!("wire of {:.1} tiles", dist(points[a], points[b])));
            }
            net.wire(spec.members[a], spec.members[b]);
        }
    }

    let height = (2 * rows).max(left_rows).max(outputs.len()) as u32;
    Ok(LayoutInfo { width: (7 * segs + 7) as u32, height, poles: poles.len() })
}

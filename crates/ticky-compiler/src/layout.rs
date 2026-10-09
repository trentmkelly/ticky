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
    /// Medium poles for power.
    pub poles: usize,
    /// Medium poles that only carry long circuit wires.
    pub relays: usize,
    /// Medium poles of the output return lines.
    pub carriers: usize,
    /// For each output port with a return line: (port, the line's last pole).
    pub line_ends: Vec<(EntId, EntId)>,
}

pub struct LayoutOpts {
    /// Medium poles for power.
    pub poles: bool,
    /// Return lines that bring every output back to the west edge, each on its own wires.
    pub outputs_west: bool,
}

pub fn layout(net: &mut Netlist, nets: &[crate::codegen::NetSpec], opts: &LayoutOpts) -> Result<LayoutInfo, String> {
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
    let east = !outputs.is_empty();
    if east {
        for (i, &id) in outputs.iter().enumerate() {
            net.entities[id].pos = (w + 1.0, i as f64 + 0.5);
        }
        // With return lines, the column next to the ports is theirs: power from one further.
        let px = if opts.outputs_west { w + 3.5 } else { w + 2.5 };
        for k in 0..outputs.len().div_ceil(7) {
            poles.push((px, 7.0 * k as f64 + 3.5));
        }
    }

    if !opts.poles {
        poles.clear();
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

    // Return lines: each output's signal runs on its own chain of poles (red wire) north of
    // the blueprint and back west to a pole above the inputs. The first output's line is
    // the northernmost, so the lines nest without crossing.
    let mut lines: Vec<(EntId, Vec<(f64, f64)>)> = Vec::new();
    if opts.outputs_west {
        let n = outputs.len();
        for (i, &id) in outputs.iter().enumerate() {
            let row = -((n - i) as f64) + 0.5;
            let mut pts = vec![(w + 2.5, i as f64 + 0.5), (w + 2.5, row)];
            let mut x = w + 2.5;
            while x - 8.0 > -2.5 {
                x -= 8.0;
                pts.push((x, row));
            }
            pts.push((-2.5, row));
            lines.push((id, pts));
        }
    }

    // Occupied tiles, for placing relay poles.
    let mut used: std::collections::HashSet<(i64, i64)> = std::collections::HashSet::new();
    for i in 0..net.entities.len() {
        let (w, h) = net.footprint(i);
        let (cx, cy) = net.entities[i].pos;
        let (x0, y0) = ((cx - w as f64 / 2.0).round() as i64, (cy - h as f64 / 2.0).round() as i64);
        for dx in 0..w as i64 {
            for dy in 0..h as i64 {
                used.insert((x0 + dx, y0 + dy));
            }
        }
    }
    let tile = |p: (f64, f64)| (p.0.floor() as i64, p.1.floor() as i64);
    for (_, pts) in &lines {
        for p in pts {
            used.insert(tile(*p));
        }
    }
    let mut relays = 0;
    let mut carriers = 0;
    let mut line_ends = Vec::new();
    for (port, pts) in &lines {
        let mut prev = (*port, Conn::OutRed);
        let mut prev_pos = net.entities[*port].pos;
        for &p in pts {
            // The climb can be longer than one wire: relay through free tiles on the way.
            while dist(prev_pos, p) > MAX_WIRE {
                let t = free_tile(&used, prev_pos, p).ok_or_else(|| format!("no room for an output line near {prev_pos:?}"))?;
                used.insert(t);
                let pos = (t.0 as f64 + 0.5, t.1 as f64 + 0.5);
                let id = net.add(Kind::Pole, Role::Power);
                net.entities[id].pos = pos;
                net.wire(prev, (id, Conn::Red));
                prev = (id, Conn::Red);
                prev_pos = pos;
                carriers += 1;
            }
            let id = net.add(Kind::Pole, Role::Power);
            net.entities[id].pos = p;
            net.wire(prev, (id, Conn::Red));
            prev = (id, Conn::Red);
            prev_pos = p;
            carriers += 1;
        }
        line_ends.push((*port, prev.0));
    }
    for spec in nets {
        let points: Vec<(f64, f64)> = spec.members.iter().map(|(e, _)| net.entities[*e].pos).collect();
        for (a, b) in mst(&points) {
            let d = dist(points[a], points[b]);
            if d <= MAX_WIRE {
                net.wire(spec.members[a], spec.members[b]);
                continue;
            }
            // Too far for one wire: relay through medium poles on free tiles, each the free
            // tile within reach that gets closest to the far end.
            let conn = if spec.red { Conn::Red } else { Conn::Green };
            let mut prev = spec.members[a];
            let mut prev_pos = points[a];
            while dist(prev_pos, points[b]) > MAX_WIRE {
                let tile = free_tile(&used, prev_pos, points[b]).ok_or_else(|| format!("no room for a wire relay near {prev_pos:?}"))?;
                used.insert(tile);
                let pos = (tile.0 as f64 + 0.5, tile.1 as f64 + 0.5);
                let id = net.add(Kind::Pole, Role::Power);
                net.entities[id].pos = pos;
                net.entities[id].description = Some("Ticky wire relay".into());
                net.wire(prev, (id, conn));
                prev = (id, conn);
                prev_pos = pos;
                relays += 1;
            }
            net.wire(prev, spec.members[b]);
        }
    }

    let height = (2 * rows).max(left_rows).max(outputs.len()) + if opts.outputs_west { outputs.len() } else { 0 };
    let width = 7 * segs + 4 + if east { 3 } else { 0 } + if opts.outputs_west { 1 } else { 0 };
    Ok(LayoutInfo { width: width as u32, height: height as u32, poles: poles.len(), relays, carriers, line_ends })
}

/// The free tile within wire reach of `from` that is closest to `to` (and makes progress).
fn free_tile(used: &std::collections::HashSet<(i64, i64)>, from: (f64, f64), to: (f64, f64)) -> Option<(i64, i64)> {
    let r = MAX_WIRE.floor() as i64;
    let (fx, fy) = (from.0.floor() as i64, from.1.floor() as i64);
    let mut best: Option<((i64, i64), f64)> = None;
    for dx in -r..=r {
        for dy in -r..=r {
            let t = (fx + dx, fy + dy);
            let c = (t.0 as f64 + 0.5, t.1 as f64 + 0.5);
            if used.contains(&t) || dist(c, from) > MAX_WIRE {
                continue;
            }
            let d = dist(c, to);
            if best.is_none_or(|(_, bd)| d < bd) {
                best = Some((t, d));
            }
        }
    }
    best.filter(|(_, d)| *d + 1.0 < dist(from, to)).map(|(t, _)| t)
}

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
}

/// A return line: gate, output port, and the poles in between.
type Line = (EntId, EntId, Vec<(f64, f64)>);

pub struct LayoutOpts {
    /// Medium poles for power.
    pub poles: bool,
    /// Output ports at the west edge, fed by return lines.
    pub outputs_west: bool,
    /// Experimental placement by simulated annealing instead of the grid.
    pub anneal: Option<crate::place::AnnealOpts>,
}

/// An annealed placement: the slot grid and each entity's slot.
type Placed = (crate::place::Slots, Vec<(usize, usize)>);

pub fn layout(net: &mut Netlist, nets: &[crate::codegen::NetSpec], opts: &LayoutOpts) -> Result<LayoutInfo, String> {
    let core: Vec<EntId> = (0..net.entities.len()).filter(|&i| net.entities[i].role == Role::Core).collect();
    let inputs: Vec<EntId> =
        (0..net.entities.len()).filter(|&i| matches!(net.entities[i].role, Role::InputPort { .. })).collect();
    let outputs: Vec<EntId> =
        (0..net.entities.len()).filter(|&i| matches!(net.entities[i].role, Role::OutputPort { .. })).collect();
    // With return lines, the gates take the output ports' places on the east edge.
    let gates: Vec<EntId> =
        (0..net.entities.len()).filter(|&i| matches!(net.entities[i].role, Role::OutputGate { .. })).collect();
    let east_col: &[EntId] = if opts.outputs_west { &gates } else { &outputs };
    let run = net.find_role(|r| *r == Role::RunSwitch);

    // Left: RUN switch above the input ports (placed first: the annealer counts their wires).
    if let Some(r) = run {
        net.entities[r].pos = (-1.5, 0.5);
    }
    for (i, &id) in inputs.iter().enumerate() {
        net.entities[id].pos = (-2.0, i as f64 + 1.5);
    }

    let n = core.len().max(1);
    // `segs` segments of 7 columns (6 slots and a pole column), `rows` rows 2 tiles tall,
    // `w` tiles wide.
    let (segs, rows, w) = match opts.anneal {
        None => {
            // Roughly square, serpentine so consecutive entities (which share private wires)
            // stay adjacent.
            let segs = ((n as f64 / 21.0).sqrt().ceil() as usize).max(1);
            let per_row = SEG * segs;
            let rows = n.div_ceil(per_row);
            for (k, &id) in core.iter().enumerate() {
                let (r, j) = (k / per_row, k % per_row);
                let j = if r % 2 == 1 { per_row - 1 - j } else { j };
                let (seg, off) = (j / SEG, j % SEG);
                let col = seg * 7 + if off < 3 { off } else { off + 1 };
                // Two-tile combinators fill the slot; one-tile entities sit in its top half.
                let dy = if net.entities[id].kind.is_combinator() { 1.0 } else { 0.5 };
                net.entities[id].pos = (col as f64 + 0.5, 2.0 * r as f64 + dy);
            }
            (segs, rows, 7 * segs)
        }
        Some(a) => {
            // Wire networks as member lists, counting only entities with a position yet.
            let known: std::collections::HashSet<EntId> =
                core.iter().copied().chain(run).chain(inputs.iter().copied()).collect();
            let members: Vec<Vec<EntId>> =
                nets.iter().map(|n| n.members.iter().map(|(e, _)| *e).filter(|e| known.contains(e)).collect()).collect();
            // Limits are for the whole blueprint: leave room for the ports at the edges.
            use crate::place::Objective;
            let edge_w = 4 + if east_col.is_empty() { 0 } else { 3 } + if opts.outputs_west { 1 } else { 0 };
            let edge_h = if opts.outputs_west { outputs.len() } else { 0 };
            let objective = match a.objective {
                Objective::MaxWidth(w) => Objective::MaxWidth(w.saturating_sub(edge_w as u32).max(1)),
                Objective::MaxHeight(h) => Objective::MaxHeight(h.saturating_sub(edge_h as u32).max(2)),
                o => o,
            };
            let a = crate::place::AnnealOpts { objective, ..a };
            let frame = crate::place::Frame { extra_w: edge_w, extra_h: edge_h, min_h: (inputs.len() + 1).max(east_col.len()) };
            // For the smallest footprint, try a few block shapes (the grid layout's width, the
            // best area within 2:1, a square block) and keep the smallest blueprint.
            let candidates: Vec<Option<usize>> = match a.objective {
                Objective::Area => {
                    let grid_cols = SEG * ((n as f64 / 21.0).sqrt().ceil() as usize).max(1);
                    vec![Some(grid_cols.min(n)), None, Some(((2.0 * n as f64).sqrt().ceil() as usize).max(1))]
                }
                _ => vec![None],
            };
            let mut best: Option<(usize, Placed)> = None;
            for c in candidates {
                let (slots, placed) = crate::place::anneal(net, &members, &core, opts.poles, a, frame, c);
                let cols = placed.iter().map(|p| p.0 + 1).max().unwrap_or(1);
                let rows = placed.iter().map(|p| p.1 + 1).max().unwrap_or(1);
                let w = if opts.poles { 7 * cols.div_ceil(SEG) } else { slots.tile_x(cols - 1) + 1 };
                let area = (w + edge_w) * ((2 * rows).max(frame.min_h) + edge_h);
                if best.as_ref().is_none_or(|b| area < b.0) {
                    best = Some((area, (slots, placed)));
                }
            }
            let (_, (slots, placed)) = best.unwrap();
            let cols = placed.iter().map(|p| p.0 + 1).max().unwrap_or(1);
            let rows = placed.iter().map(|p| p.1 + 1).max().unwrap_or(1);
            for (&id, &(c, r)) in core.iter().zip(&placed) {
                let dy = if net.entities[id].kind.is_combinator() { 1.0 } else { 0.5 };
                net.entities[id].pos = (slots.tile_x(c) as f64 + 0.5, 2.0 * r as f64 + dy);
            }
            let segs = cols.div_ceil(SEG);
            (segs, rows, if opts.poles { 7 * segs } else { slots.tile_x(cols - 1) + 1 })
        }
    };
    let mut poles: Vec<(f64, f64)> = Vec::new();
    // A pole in row r powers rows r-2..=r+1.
    let mut pole_rows: Vec<usize> = (0..rows.div_ceil(4)).map(|b| (4 * b + 2).min(rows - 1)).collect();
    pole_rows.dedup();
    for &r in &pole_rows {
        for seg in 0..segs {
            poles.push(((seg * 7 + 3) as f64 + 0.5, 2.0 * r as f64 + 0.5));
        }
    }

    // Poles one column left of the inputs.
    let left_rows = inputs.len() + 1;
    // A pole powers 3 rows either side of its own.
    for k in 0..left_rows.div_ceil(7).max(1) {
        poles.push((-3.5, 7.0 * k as f64 + 3.5));
    }

    // Right: output ports just past the last core column.
    let w = w as f64;
    let east = !east_col.is_empty();
    if east {
        for (i, &id) in east_col.iter().enumerate() {
            net.entities[id].pos = (w + 1.0, i as f64 + 0.5);
        }
        // With return lines, the column next to the ports is theirs: power from one further.
        let px = if opts.outputs_west { w + 3.5 } else { w + 2.5 };
        for k in 0..east_col.len().div_ceil(7) {
            poles.push((px, 7.0 * k as f64 + 3.5));
        }
    }
    // Output ports on the west edge, one row each north of the blueprint (the first output
    // northernmost), facing west; powered by poles further west.
    let n_out = outputs.len();
    if opts.outputs_west {
        for (i, &id) in outputs.iter().enumerate() {
            net.entities[id].pos = (-2.0, -((n_out - i) as f64) + 0.5);
            net.entities[id].dir = Dir::West;
        }
        for k in 0..n_out.div_ceil(7) {
            poles.push((-3.5, -(7.0 * k as f64) - 3.5));
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

    // Return lines: each gate's result runs on its own chain of poles (red wire) north and
    // then west, to its output port. The first output's line is the northernmost, so the
    // lines nest without crossing.
    let mut lines: Vec<Line> = Vec::new();
    if opts.outputs_west {
        for (i, (&gate, &port)) in gates.iter().zip(&outputs).enumerate() {
            let row = -((n_out - i) as f64) + 0.5;
            let mut pts = vec![(w + 2.5, i as f64 + 0.5), (w + 2.5, row)];
            let mut x = w + 2.5;
            while x - 8.0 > -0.5 {
                x -= 8.0;
                pts.push((x, row));
            }
            pts.push((-0.5, row));
            lines.push((gate, port, pts));
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
    for (_, _, pts) in &lines {
        for p in pts {
            used.insert(tile(*p));
        }
    }
    let mut relays = 0;
    let mut carriers = 0;
    for (gate, port, pts) in &lines {
        let mut prev = (*gate, Conn::OutRed);
        let mut prev_pos = net.entities[*gate].pos;
        for &p in pts {
            // The climb can be longer than one wire: relay through free tiles on the way.
            for t in route(&|t| !used.contains(&t), prev_pos, p).ok_or_else(|| format!("no room for an output line near {prev_pos:?}"))? {
                used.insert(t);
                let pos = (t.0 as f64 + 0.5, t.1 as f64 + 0.5);
                let id = net.add(Kind::Pole, Role::Power);
                net.entities[id].pos = pos;
                net.wire(prev, (id, Conn::Red));
                prev = (id, Conn::Red);
                carriers += 1;
            }
            let id = net.add(Kind::Pole, Role::Power);
            net.entities[id].pos = p;
            net.wire(prev, (id, Conn::Red));
            prev = (id, Conn::Red);
            prev_pos = p;
            carriers += 1;
        }
        net.wire(prev, (*port, Conn::InRed));
    }
    // Poles (power, output lines) by tile, with whether their red and green connectors are
    // taken: a relay can use a pole whose connector of the wire's colour is free.
    let mut pole_at: std::collections::HashMap<(i64, i64), (EntId, [bool; 2])> = std::collections::HashMap::new();
    for (i, e) in net.entities.iter().enumerate() {
        if matches!(e.kind, Kind::Pole) {
            pole_at.insert(tile(e.pos), (i, [false, false]));
        }
    }
    for w in &net.wires {
        for (e, c) in [w.a, w.b] {
            if matches!(net.entities[e].kind, Kind::Pole) {
                if let Some(p) = pole_at.get_mut(&tile(net.entities[e].pos)) {
                    p.1[(c == Conn::Green) as usize] = true;
                }
            }
        }
    }
    for spec in nets {
        let points: Vec<(f64, f64)> = spec.members.iter().map(|(e, _)| net.entities[*e].pos).collect();
        for (a, b) in mst(&points) {
            let d = dist(points[a], points[b]);
            if d <= MAX_WIRE {
                net.wire(spec.members[a], spec.members[b]);
                continue;
            }
            // Too far for one wire: relay through the fewest medium poles on free tiles.
            let conn = if spec.red { Conn::Red } else { Conn::Green };
            let mut prev = spec.members[a];
            let ci = (conn == Conn::Green) as usize;
            let free = |t: (i64, i64)| !used.contains(&t) || pole_at.get(&t).is_some_and(|p| !p.1[ci]);
            let path = route(&free, points[a], points[b]).ok_or_else(|| format!("no room for a wire relay near {:?}", points[a]))?;
            for tile in path {
                let id = match pole_at.get_mut(&tile) {
                    Some(p) => {
                        p.1[ci] = true;
                        p.0
                    }
                    None => {
                        used.insert(tile);
                        let id = net.add(Kind::Pole, Role::Power);
                        net.entities[id].pos = (tile.0 as f64 + 0.5, tile.1 as f64 + 0.5);
                        net.entities[id].description = Some("Ticky wire relay".into());
                        relays += 1;
                        let mut taken = [false, false];
                        taken[ci] = true;
                        pole_at.insert(tile, (id, taken));
                        id
                    }
                };
                net.wire(prev, (id, conn));
                prev = (id, conn);
            }
            net.wire(prev, spec.members[b]);
        }
    }

    let height = (2 * rows).max(left_rows).max(east_col.len()) + if opts.outputs_west { n_out } else { 0 };
    let width = w as usize + 4 + if east { 3 } else { 0 } + if opts.outputs_west { 1 } else { 0 };
    Ok(LayoutInfo { width: width as u32, height: height as u32, poles: poles.len(), relays, carriers })
}

/// Relay tiles for a wire from `from` to `to`: the fewest free tiles such that every hop is
/// within reach (breadth-first over free tiles, going around occupied areas if needed).
/// Empty if `to` is already in reach; `None` if there's no way through.
fn route(free: &dyn Fn((i64, i64)) -> bool, from: (f64, f64), to: (f64, f64)) -> Option<Vec<(i64, i64)>> {
    if dist(from, to) <= MAX_WIRE {
        return Some(vec![]);
    }
    let centre = |t: (i64, i64)| (t.0 as f64 + 0.5, t.1 as f64 + 0.5);
    // Search the area around both ends, with room to go around.
    let margin = 2 * MAX_WIRE as i64 + 2;
    let (x0, x1) = (from.0.min(to.0) as i64 - margin, from.0.max(to.0) as i64 + margin);
    let (y0, y1) = (from.1.min(to.1) as i64 - margin, from.1.max(to.1) as i64 + margin);
    let r = MAX_WIRE.floor() as i64;
    let mut prev: std::collections::HashMap<(i64, i64), Option<(i64, i64)>> = std::collections::HashMap::new();
    let mut queue = std::collections::VecDeque::new();
    let near = |p: (f64, f64)| {
        let (px, py) = (p.0.floor() as i64, p.1.floor() as i64);
        (-r..=r).flat_map(move |dx| (-r..=r).map(move |dy| (px + dx, py + dy)))
    };
    for t in near(from) {
        if free(t) && dist(centre(t), from) <= MAX_WIRE && !prev.contains_key(&t) {
            prev.insert(t, None);
            queue.push_back(t);
        }
    }
    while let Some(t) = queue.pop_front() {
        if dist(centre(t), to) <= MAX_WIRE {
            let mut path = vec![t];
            let mut cur = t;
            while let Some(Some(p)) = prev.get(&cur) {
                path.push(*p);
                cur = *p;
            }
            path.reverse();
            return Some(path);
        }
        for u in near(centre(t)) {
            if u.0 < x0 || u.0 > x1 || u.1 < y0 || u.1 > y1 || !free(u) || prev.contains_key(&u) {
                continue;
            }
            if dist(centre(u), centre(t)) <= MAX_WIRE {
                prev.insert(u, Some(t));
                queue.push_back(u);
            }
        }
    }
    None
}

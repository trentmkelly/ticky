//! Duplicating cheap drivers to save wire relays (PLAN.md section 9).
//!
//! A wire network whose members end up in two distant clusters needs relay poles between
//! them. When the network has a single driver that is cheap and pure (one arithmetic,
//! decider or non-random selector combinator, or a constant combinator), a copy of the
//! driver beside the far cluster can feed it instead: the copy reads the same input networks,
//! so it computes the same value on the same tick, and the far cluster moves to a network of
//! its own driven by the copy.
//!
//! After placement and routing, [`improve`] tries the relayed networks one at a time (most
//! relays first): the members across the longest spanning-tree hop from the driver go to a
//! copy on the free tile (free pair of tiles for a two-tile combinator, powered when there
//! are poles) inside the block that needs the fewest relays for the copy's share of the
//! network and for reaching the driver's input networks. Everything is routed again, and the
//! copy stays only if it saves at least two relays (more entities than it adds) and nothing
//! sticks out further than before, so placement never gets worse; the rest of the placement
//! doesn't move. On by default with `--place=anneal`, `--duplicate-drivers` with the grid.
//! `TICKY_DUP=0`/`1` overrides that (for measuring); `TICKY_DUP_STATS=1` reports relayed
//! networks by verdict and what was kept (`2`: every network and attempt).
//!
//! Never duplicated: anything that feeds itself (an output network that is also one of its
//! input networks: memory cells, counters), random selectors (their copies would pick
//! differently), and anything that isn't an internal combinator (ports, gates, the RUN
//! switch, controls, which the player or the outside world drive).

use ticky_factorio::{Conn, EntId, Kind, Netlist, Role, Selector};

use crate::codegen::NetSpec;

/// One duplication: the network, its driver, and the members the copy takes over.
#[derive(Clone, Debug)]
pub struct Cand {
    pub net: usize,
    pub driver: EntId,
    pub moved: Vec<(EntId, Conn)>,
}

fn dist(a: (f64, f64), b: (f64, f64)) -> f64 {
    ((a.0 - b.0).powi(2) + (a.1 - b.1).powi(2)).sqrt()
}

/// Whether a member drives its network (an output connector, or a constant combinator).
fn drives(net: &Netlist, m: (EntId, Conn)) -> bool {
    matches!(m.1, Conn::OutRed | Conn::OutGreen) || matches!(net.entities[m.0].kind, Kind::Constant(_))
}

/// Whether `e` may be copied: an internal, stateless combinator that doesn't feed itself.
fn pure_kind(net: &Netlist, e: EntId) -> bool {
    net.entities[e].role == Role::Core
        && match &net.entities[e].kind {
            Kind::Arith(_) | Kind::Decider(_) | Kind::Constant(_) => true,
            Kind::Selector(s) => !matches!(s, Selector::Random { .. }),
            _ => false,
        }
}

/// The network each connector is on (`None` for connectors on two networks, which we leave
/// alone).
fn conn_nets(nets: &[NetSpec]) -> std::collections::HashMap<(EntId, Conn), Option<usize>> {
    let mut of: std::collections::HashMap<(EntId, Conn), Option<usize>> = std::collections::HashMap::new();
    for (ni, spec) in nets.iter().enumerate() {
        for &m in &spec.members {
            of.entry(m).and_modify(|v| *v = None).or_insert(Some(ni));
        }
    }
    of
}

/// Why a relayed network can't have its driver duplicated (for the measurement report).
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Verdict {
    Ok,
    /// More than one driver (a wire sum, the bus).
    Drivers,
    /// The driver is a port, gate, switch or control.
    External,
    /// Random selector.
    Random,
    /// The driver feeds itself (memory, counter).
    Feedback,
    /// A connector shared between network specs.
    Odd,
}

/// Whether network `ni`'s driver may be duplicated, and which entity it is.
pub fn verdict(net: &Netlist, nets: &[NetSpec], of: &std::collections::HashMap<(EntId, Conn), Option<usize>>, ni: usize) -> (Verdict, Option<EntId>) {
    let spec = &nets[ni];
    let drivers: Vec<(EntId, Conn)> = spec.members.iter().copied().filter(|&m| drives(net, m)).collect();
    if drivers.len() != 1 {
        return (Verdict::Drivers, None);
    }
    let d = drivers[0].0;
    if spec.members.iter().filter(|m| m.0 == d).count() > 1 {
        return (Verdict::Feedback, Some(d));
    }
    if net.entities[d].role != Role::Core {
        return (Verdict::External, Some(d));
    }
    if !pure_kind(net, d) {
        return (Verdict::Random, Some(d));
    }
    let ins: Vec<Option<usize>> = [Conn::InRed, Conn::InGreen].iter().filter_map(|&c| of.get(&(d, c)).copied()).collect();
    let outs: Vec<Option<usize>> =
        [Conn::OutRed, Conn::OutGreen, Conn::Red, Conn::Green].iter().filter_map(|&c| of.get(&(d, c)).copied()).collect();
    if ins.iter().chain(&outs).any(|x| x.is_none()) {
        return (Verdict::Odd, Some(d));
    }
    if ins.iter().any(|i| outs.contains(i)) {
        return (Verdict::Feedback, Some(d));
    }
    (Verdict::Ok, Some(d))
}

/// Candidates among the networks that got relays (`relays[ni]` > 0), placed as in `net`:
/// the members across the longest spanning-tree hop from the driver go to a copy.
pub fn candidates(net: &Netlist, nets: &[NetSpec], relays: &[usize]) -> Vec<Cand> {
    let of = conn_nets(nets);
    let mut out = Vec::new();
    for ni in 0..nets.len().min(relays.len()) {
        if relays[ni] == 0 {
            continue;
        }
        let (Verdict::Ok, Some(d)) = verdict(net, nets, &of, ni) else { continue };
        let spec = &nets[ni];
        let pts: Vec<(f64, f64)> = spec.members.iter().map(|m| net.entities[m.0].pos).collect();
        let edges = crate::layout::mst(&pts);
        let Some(&(a, b)) = edges.iter().max_by(|x, y| dist(pts[x.0], pts[x.1]).total_cmp(&dist(pts[y.0], pts[y.1]))) else { continue };
        // The component of the tree (without the longest hop) holding the driver stays.
        let k = pts.len();
        let mut adj = vec![Vec::new(); k];
        for &(x, y) in &edges {
            if (x, y) != (a, b) {
                adj[x].push(y);
                adj[y].push(x);
            }
        }
        let di = spec.members.iter().position(|m| m.0 == d).unwrap();
        let mut keep = vec![false; k];
        let mut stack = vec![di];
        keep[di] = true;
        while let Some(x) = stack.pop() {
            for &y in &adj[x] {
                if !keep[y] {
                    keep[y] = true;
                    stack.push(y);
                }
            }
        }
        let moved: Vec<(EntId, Conn)> = (0..k).filter(|&i| !keep[i]).map(|i| spec.members[i]).collect();
        if moved.is_empty() {
            continue;
        }
        out.push(Cand { net: ni, driver: d, moved });
    }
    out
}

/// Adds the copy of `c.driver` and moves `c.moved` to a new network it drives. Returns the
/// copy.
pub fn apply(net: &mut Netlist, nets: &mut Vec<NetSpec>, c: &Cand) -> EntId {
    let e = net.entities[c.driver].clone();
    let copy = net.add(e.kind.clone(), Role::Core);
    net.entities[copy].dir = e.dir;
    net.entities[copy].description = Some(match &e.description {
        Some(d) => format!("{d} (copy, saves wire relays)"),
        None => "(copy, saves wire relays)".into(),
    });
    let spec = &mut nets[c.net];
    let out_conn = spec.members.iter().find(|m| m.0 == c.driver).unwrap().1;
    spec.members.retain(|m| !c.moved.contains(m));
    let red = spec.red;
    let mut members = vec![(copy, out_conn)];
    members.extend(c.moved.iter().copied());
    nets.push(NetSpec { red, members });
    // The copy reads whatever networks the driver reads now (an earlier duplication may
    // have moved the driver's input to its copy's network).
    for conn in [Conn::InRed, Conn::InGreen] {
        if let Some(i) = nets.iter().position(|n| n.members.contains(&(c.driver, conn))) {
            nets[i].members.push((copy, conn));
        }
    }
    copy
}

/// Longest wire we allow ourselves (as in the layout).
const MAX_WIRE: f64 = 8.5;

/// Relay poles a hop of `d` tiles needs at least.
fn hops(d: f64) -> usize {
    if d <= MAX_WIRE { 0 } else { (d / MAX_WIRE).ceil() as usize - 1 }
}

/// Relays a network over `pts` needs at least (along its spanning tree).
fn tree_hops(pts: &[(f64, f64)]) -> usize {
    crate::layout::mst(pts).iter().map(|&(a, b)| hops(dist(pts[a], pts[b]))).sum()
}

type Tiles = std::collections::HashSet<(i64, i64)>;

/// Routes every network of a placed netlist (with its poles); relays per network, or `None`
/// if some network found no room.
pub type Route<'a> = dyn Fn(&mut Netlist, &[NetSpec], &Tiles) -> Option<Vec<usize>> + 'a;

/// What the layout knows about the block: tiles taken before routing, tiles fixed
/// peripherals keep free, the block's bounding box (copies stay inside it, so the footprint
/// doesn't grow), whether combinators need power poles, and the router.
pub struct Env<'a> {
    pub used: &'a Tiles,
    pub reserved: &'a Tiles,
    pub bbox: (i64, i64, i64, i64),
    pub poles: bool,
    pub route: &'a Route<'a>,
}

/// Duplications tried, at most.
const MAX_TRIALS: usize = 64;

/// The tiles an entity (two tiles tall if `tall`) with its top tile at `t` takes.
fn tiles_of(t: (i64, i64), tall: bool) -> Vec<(i64, i64)> {
    if tall { vec![t, (t.0, t.1 + 1)] } else { vec![t] }
}

/// The best free spot for the copy in `c` (its centre): within the block, on free tiles,
/// powered if it needs power, fewest estimated relays for the copy's networks (its share of
/// the network, and reaching each input network), then nearest its members.
fn spot(pre: &Netlist, nets: &[NetSpec], used: &Tiles, env: &Env, c: &Cand) -> Option<(f64, f64)> {
    let tall = pre.entities[c.driver].kind.is_combinator();
    let moved: Vec<(f64, f64)> = c.moved.iter().map(|m| pre.entities[m.0].pos).collect();
    let inputs: Vec<Vec<(f64, f64)>> = [Conn::InRed, Conn::InGreen]
        .iter()
        .filter_map(|&cc| nets.iter().find(|n| n.members.contains(&(c.driver, cc))))
        .map(|n| n.members.iter().map(|m| pre.entities[m.0].pos).collect())
        .collect();
    let poles: Vec<(f64, f64)> = pre.entities.iter().filter(|e| matches!(e.kind, Kind::Pole)).map(|e| e.pos).collect();
    let supply = ticky_factorio::netlist::POLE_SUPPLY;
    let (x0, y0, x1, y1) = env.bbox;
    let r = MAX_WIRE as i64;
    let mut seen = Tiles::new();
    let mut best: Option<((usize, f64), (f64, f64))> = None;
    for p in &moved {
        let (px, py) = (p.0.floor() as i64, p.1.floor() as i64);
        for x in (px - r).max(x0)..=(px + r).min(x1) {
            for y in (py - r).max(y0)..=(py + r).min(y1 - tall as i64) {
                if !seen.insert((x, y)) {
                    continue;
                }
                if tiles_of((x, y), tall).iter().any(|t| used.contains(t) || env.reserved.contains(t)) {
                    continue;
                }
                let centre = (x as f64 + 0.5, y as f64 + if tall { 1.0 } else { 0.5 });
                if env.poles && tall && !poles.iter().any(|q| (centre.0 - q.0).abs() < supply + 0.5 && (centre.1 - q.1).abs() < supply + 1.0) {
                    continue;
                }
                let mut pts = moved.clone();
                pts.push(centre);
                let est = tree_hops(&pts)
                    + inputs.iter().map(|ms| hops(ms.iter().map(|m| dist(*m, centre)).fold(f64::INFINITY, f64::min))).sum::<usize>();
                let near: f64 = moved.iter().map(|m| dist(*m, centre)).sum();
                if best.is_none_or(|b| (est, near) < b.0) {
                    best = Some(((est, near), centre));
                }
            }
        }
    }
    best.map(|b| b.1)
}

/// The bounding box of everything placed (tile edges).
fn extent(net: &Netlist) -> (f64, f64, f64, f64) {
    let mut b = (f64::MAX, f64::MAX, f64::MIN, f64::MIN);
    for i in 0..net.entities.len() {
        let (w, h) = net.footprint(i);
        let (cx, cy) = net.entities[i].pos;
        b = (b.0.min(cx - w as f64 / 2.0), b.1.min(cy - h as f64 / 2.0), b.2.max(cx + w as f64 / 2.0), b.3.max(cy + h as f64 / 2.0));
    }
    b
}

/// Copies cheap drivers of relayed networks (one at a time, most relays first) onto free
/// tiles beside their far members, and keeps each copy only if the relays it saves are more
/// than the one entity it adds and nothing grows the blueprint's extent. `pre` is the placed
/// netlist before routing, `routed` after (with `relays` per network). Returns the routed
/// netlist and the relays per network if anything was kept.
pub fn improve(pre: &Netlist, routed: &Netlist, nets: &[NetSpec], relays: &[usize], env: &Env) -> Option<(Netlist, Vec<usize>)> {
    // A circuit wire laid outside `nets` (output return lines) is left alone: only nets'
    // members can be copied or moved, and those never sit on a line.
    let (mut pre, mut nets, mut used) = (pre.clone(), nets.to_vec(), env.used.clone());
    let mut routed = routed.clone();
    let mut relays = relays.to_vec();
    let mut rejected: std::collections::HashSet<(usize, EntId)> = std::collections::HashSet::new();
    let (mut kept, before) = (0, relays.iter().sum::<usize>());
    for _ in 0..MAX_TRIALS {
        // A copy pays only if it saves two relays or more.
        if relays.iter().sum::<usize>() < 2 {
            break;
        }
        let mut cands: Vec<Cand> = candidates(&routed, &nets, &relays).into_iter().filter(|c| !rejected.contains(&(c.net, c.driver))).collect();
        cands.sort_by_key(|c| (std::cmp::Reverse(relays[c.net]), c.net));
        let Some(c) = cands.into_iter().next() else { break };
        rejected.insert((c.net, c.driver));
        let Some(pos) = spot(&pre, &nets, &used, env, &c) else {
            if std::env::var("TICKY_DUP_STATS").as_deref() == Ok("2") {
                eprintln!("dup try net {} driver {}: no spot", c.net, c.driver);
            }
            continue;
        };
        let (mut p2, mut n2, mut u2) = (pre.clone(), nets.clone(), used.clone());
        let copy = apply(&mut p2, &mut n2, &c);
        p2.entities[copy].pos = pos;
        p2.entities[copy].dir = ticky_factorio::Dir::North;
        let tall = p2.entities[copy].kind.is_combinator();
        u2.extend(tiles_of((pos.0.floor() as i64, (pos.1 - if tall { 1.0 } else { 0.5 }).round() as i64), tall));
        let mut r2 = p2.clone();
        let Some(rel) = (env.route)(&mut r2, &n2, &u2) else { continue };
        let (a, b) = (extent(&r2), extent(&routed));
        let inside = a.0 >= b.0 && a.1 >= b.1 && a.2 <= b.2 && a.3 <= b.3;
        if std::env::var("TICKY_DUP_STATS").as_deref() == Ok("2") {
            eprintln!("dup try net {} driver {} at {pos:?}: relays {} → {}, inside {inside}", c.net, c.driver, relays.iter().sum::<usize>(), rel.iter().sum::<usize>());
        }
        if inside && rel.iter().sum::<usize>() + 1 < relays.iter().sum::<usize>() {
            (pre, nets, used, routed, relays) = (p2, n2, u2, r2, rel);
            kept += 1;
            // Routes changed: what didn't pay before may now.
            rejected.clear();
        }
    }
    if std::env::var_os("TICKY_DUP_STATS").is_some() {
        eprintln!("dup: kept {kept} copies, relays {} → {}", before, relays.iter().sum::<usize>());
    }
    (kept > 0).then_some((routed, relays))
}

/// The measurement report (`TICKY_DUP_STATS=1`): relayed networks by verdict, with relays.
pub fn report(net: &Netlist, nets: &[NetSpec], relays: &[usize]) -> String {
    let of = conn_nets(nets);
    let mut by: std::collections::BTreeMap<String, (usize, usize)> = std::collections::BTreeMap::new();
    let mut total = 0;
    let mut r_detail: Vec<String> = Vec::new();
    for ni in 0..relays.len() {
        if relays[ni] == 0 {
            continue;
        }
        total += relays[ni];
        let key = if ni >= nets.len() {
            "gate line".to_string()
        } else {
            let (v, d) = verdict(net, nets, &of, ni);
            match (v, d) {
                (Verdict::Ok, Some(d)) => {
                    let kind = match &net.entities[d].kind {
                        Kind::Constant(_) => "constant",
                        Kind::Arith(_) => "arith",
                        Kind::Decider(_) => "decider",
                        _ => "selector",
                    };
                    // Are its inputs at hand everywhere? The bus (net 0) or none at all.
                    let ins: Vec<usize> = [Conn::InRed, Conn::InGreen].iter().filter_map(|&c| of.get(&(d, c)).copied().flatten()).collect();
                    let avail = if ins.iter().all(|&i| i == 0) {
                        "inputs: none/bus"
                    } else if ins.iter().any(|&i| relays.get(i).copied().unwrap_or(0) > 0) {
                        "inputs: relayed"
                    } else {
                        "inputs: local"
                    };
                    format!("ok {kind} ({avail})")
                }
                (v, _) => format!("{v:?}"),
            }
        };
        if std::env::var("TICKY_DUP_STATS").as_deref() == Ok("2") && ni < nets.len() {
            let desc: Vec<String> = nets[ni]
                .members
                .iter()
                .map(|&(e, c)| {
                    let shared: Vec<usize> = nets.iter().enumerate().filter(|(j, n)| *j != ni && n.members.contains(&(e, c))).map(|x| x.0).collect();
                    let ins: Vec<String> = [Conn::InRed, Conn::InGreen, Conn::OutRed, Conn::OutGreen]
                        .iter()
                        .map(|&cc| format!("{:?}", nets.iter().enumerate().filter(|n| n.1.members.contains(&(e, cc))).map(|x| x.0).collect::<Vec<_>>()))
                        .collect();
                    format!("{e}:{}:{:?}:{c:?}{} io={}", net.entities[e].kind.proto_name(), net.entities[e].role, if shared.is_empty() { String::new() } else { format!(" ALSO{shared:?}") }, ins.join("/"))
                })
                .collect();
            r_detail.push(format!("    net {ni} ({key}, {} relays, {}): {}\n", relays[ni], if nets[ni].red { "red" } else { "green" }, desc.join(", ")));
        }
        let s = by.entry(key).or_default();
        s.0 += 1;
        s.1 += relays[ni];
    }
    let mut r = format!("relays {total} on {} networks\n", relays.iter().filter(|&&n| n > 0).count());
    for (k, (n, rl)) in by {
        r.push_str(&format!("  {k}: {n} networks, {rl} relays\n"));
    }
    r.extend(r_detail);
    r
}

#[cfg(test)]
mod tests {
    use super::*;
    use ticky_factorio::{ArOp, Arith, ConstComb, Nets, Operand, Sig};

    fn arith(net: &mut Netlist) -> EntId {
        let a = Arith { first: Operand::Sig(Sig(1)), first_nets: Nets::RED, second: Operand::Const(1), second_nets: Nets::RED, op: ArOp::Add, out: Sig(1) };
        net.add(Kind::Arith(a), Role::Core)
    }

    /// A driver at `d`, its consumers 1 and 2 near it and 3 far away.
    fn spread(net: &mut Netlist, d: EntId, nets: &mut Vec<NetSpec>, out: Conn) -> usize {
        for (i, x) in [(1, 1.5), (2, 2.5), (3, 30.5)] {
            net.entities[i].pos = (x, 1.0);
        }
        net.entities[d].pos = (0.5, 1.0);
        nets.push(NetSpec { red: true, members: vec![(d, out), (1, Conn::InRed), (2, Conn::InRed), (3, Conn::InRed)] });
        nets.len() - 1
    }

    #[test]
    fn only_pure_single_drivers_are_copied() {
        // A pure arithmetic driver reading the green bus: the far consumer goes to a copy.
        let mut net = Netlist::default();
        let d = arith(&mut net);
        for _ in 0..3 {
            arith(&mut net);
        }
        let mut nets = vec![NetSpec { red: false, members: vec![(d, Conn::InGreen)] }];
        let ni = spread(&mut net, d, &mut nets, Conn::OutRed);
        let cands = candidates(&net, &nets, &[0, 2]);
        assert_eq!(cands.len(), 1);
        assert_eq!(cands[0].moved, vec![(3, Conn::InRed)]);
        let copy = apply(&mut net, &mut nets, &cands[0]);
        assert_eq!(nets[ni].members, vec![(d, Conn::OutRed), (1, Conn::InRed), (2, Conn::InRed)]);
        assert_eq!(nets[2].members, vec![(copy, Conn::OutRed), (3, Conn::InRed)]);
        assert!(nets[0].members.contains(&(copy, Conn::InGreen)), "the copy reads what the driver reads");

        // Feeding itself (a memory cell or counter): never.
        let mut net = Netlist::default();
        let d = arith(&mut net);
        for _ in 0..3 {
            arith(&mut net);
        }
        let mut nets = Vec::new();
        let ni = spread(&mut net, d, &mut nets, Conn::OutRed);
        nets[ni].members.push((d, Conn::InRed));
        assert_eq!(verdict(&net, &nets, &conn_nets(&nets), ni).0, Verdict::Feedback);
        assert!(candidates(&net, &nets, &[2]).is_empty());
        // Through its other colour: never either.
        let mut nets = Vec::new();
        let ni = spread(&mut net, d, &mut nets, Conn::OutRed);
        nets.push(NetSpec { red: false, members: vec![(d, Conn::OutGreen), (d, Conn::InGreen)] });
        assert_eq!(verdict(&net, &nets, &conn_nets(&nets), ni).0, Verdict::Feedback);

        // Two drivers (a wire sum), a random selector, a port: never.
        let mut net = Netlist::default();
        let d = arith(&mut net);
        for _ in 0..4 {
            arith(&mut net);
        }
        let mut nets = Vec::new();
        let ni = spread(&mut net, d, &mut nets, Conn::OutRed);
        nets[ni].members.push((4, Conn::OutRed));
        assert_eq!(verdict(&net, &nets, &conn_nets(&nets), ni).0, Verdict::Drivers);
        nets[ni].members.pop();
        net.entities[d].kind = Kind::Selector(Selector::Random { interval: 0 });
        assert_eq!(verdict(&net, &nets, &conn_nets(&nets), ni).0, Verdict::Random);
        net.entities[d].kind = Kind::Selector(Selector::Count { out: Sig(2) });
        assert_eq!(verdict(&net, &nets, &conn_nets(&nets), ni).0, Verdict::Ok);
        net.entities[d].role = Role::RunSwitch;
        net.entities[d].kind = Kind::Constant(ConstComb { values: vec![], on: false });
        assert_eq!(verdict(&net, &nets, &conn_nets(&nets), ni).0, Verdict::External);
        net.entities[d].role = Role::Core;
        assert_eq!(verdict(&net, &nets, &conn_nets(&nets), ni).0, Verdict::Ok);
    }
}

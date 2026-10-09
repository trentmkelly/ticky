//! Experimental placement by simulated annealing (`--place=anneal`).
//!
//! The grid layout puts combinators in a serpentine in the order codegen made them, which
//! ignores who is wired to whom. Here the internal combinators are assigned to the same kind
//! of slots (one 1×2 slot per entity, in columns that leave room for power poles when there
//! are poles) by simulated annealing: repeatedly move or swap entities, keeping changes that
//! lower the cost and, with a probability that shrinks as the "temperature" falls, some that
//! raise it. The cost:
//!
//! * the footprint of the whole blueprint around the occupied slots (area, or the free side
//!   under a width/height limit). The slot grid is tight (5% spare slots): with more slack
//!   the wire costs win and the entities spread out, growing the footprint;
//! * for small wire networks: their spread (half-perimeter), plus a heavy penalty for every
//!   tile a spanning-tree hop exceeds wire reach (each such hop would need relay poles);
//! * for big networks (the bus, cluster wires): a cheap pull towards their centre.
//!
//! Ports and the RUN switch stay where the grid layout puts them; their positions count for
//! the networks they're on. Whatever is still too long afterwards gets relay poles, as usual.

use ticky_factorio::{EntId, Netlist};

/// What to minimise.
#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub enum Objective {
    /// The smallest footprint (area).
    #[default]
    Area,
    /// The shortest layout at most this many tiles wide.
    MaxWidth(u32),
    /// The narrowest layout at most this many tiles tall.
    MaxHeight(u32),
}

#[derive(Copy, Clone, Debug)]
pub struct AnnealOpts {
    pub objective: Objective,
    /// Same seed, same layout.
    pub seed: u64,
    /// Multiplies the number of moves tried.
    pub effort: f64,
}

impl Default for AnnealOpts {
    fn default() -> Self {
        AnnealOpts { objective: Objective::Area, seed: 1, effort: 1.0 }
    }
}

/// What surrounds the annealed block in the blueprint: extra width (port and gate columns),
/// extra height (output lines) and the least height (the port columns').
#[derive(Copy, Clone, Debug, Default)]
pub struct Frame {
    pub extra_w: usize,
    pub extra_h: usize,
    pub min_h: usize,
}

impl Frame {
    /// Size of the whole blueprint around a `w` × `h` block.
    fn size(&self, w: usize, h: usize) -> (usize, usize) {
        (w + self.extra_w, h.max(self.min_h) + self.extra_h)
    }

    fn area(&self, w: usize, h: usize) -> usize {
        let (w, h) = self.size(w, h);
        w * h
    }
}

/// The slot grid: `cols` slot columns of `rows` slots. With poles, every 7th tile column is
/// left for them (as in the grid layout).
pub struct Slots {
    pub cols: usize,
    pub rows: usize,
    pub poles: bool,
}

impl Slots {
    /// Tile x of a slot column.
    pub fn tile_x(&self, col: usize) -> usize {
        if self.poles {
            let (seg, off) = (col / 6, col % 6);
            seg * 7 + if off < 3 { off } else { off + 1 }
        } else {
            col
        }
    }

    /// Centre of a slot (as for a 1×2 combinator).
    fn centre(&self, s: usize) -> (f64, f64) {
        let (c, r) = (s % self.cols, s / self.cols);
        (self.tile_x(c) as f64 + 0.5, 2.0 * r as f64 + 1.0)
    }

    /// Footprint in tiles of `cols` × `rows` used slots.
    fn tiles(&self, cols: usize, rows: usize) -> (usize, usize) {
        let w = if cols == 0 { 0 } else { self.tile_x(cols - 1) + 1 };
        (w, 2 * rows)
    }
}

/// SplitMix64: small, fast, deterministic.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    fn unit(&mut self) -> f64 {
        (self.next() >> 11) as f64 / (1u64 << 53) as f64
    }
}

/// Networks with at most this many members get the exact spanning-tree cost.
const SMALL: usize = 16;
/// Weight of the pull towards the origin, per tile.
const GRAVITY: f64 = 0.3;
const MAX_WIRE: f64 = 8.5;

/// One wire network as the annealer sees it.
struct Net {
    /// Movable members (indices into `movable`).
    mov: Vec<usize>,
    /// Positions of members that don't move.
    fixed: Vec<(f64, f64)>,
    small: bool,
    weight: f64,
}

struct State<'a> {
    slots: &'a Slots,
    opts: AnnealOpts,
    frame: Frame,
    /// Slot of each movable entity, and the entity (if any) in each slot.
    at: Vec<usize>,
    who: Vec<Option<usize>>,
    col_count: Vec<usize>,
    row_count: Vec<usize>,
    nets: Vec<Net>,
    net_cost: Vec<f64>,
    /// Networks of each movable entity.
    nets_of: Vec<Vec<usize>>,
}

fn dist(a: (f64, f64), b: (f64, f64)) -> f64 {
    ((a.0 - b.0).powi(2) + (a.1 - b.1).powi(2)).sqrt()
}

impl State<'_> {
    fn pos(&self, m: usize) -> (f64, f64) {
        self.slots.centre(self.at[m])
    }

    fn net_cost(&self, j: usize) -> f64 {
        let n = &self.nets[j];
        let pts: Vec<(f64, f64)> = n.mov.iter().map(|&m| self.pos(m)).chain(n.fixed.iter().copied()).collect();
        if pts.len() < 2 {
            return 0.0;
        }
        if !n.small {
            // Spread around the centre (sum of squared distances), scaled down.
            let k = pts.len() as f64;
            let (cx, cy) = (pts.iter().map(|p| p.0).sum::<f64>() / k, pts.iter().map(|p| p.1).sum::<f64>() / k);
            let s: f64 = pts.iter().map(|p| (p.0 - cx).powi(2) + (p.1 - cy).powi(2)).sum();
            return n.weight * s / k;
        }
        // Half-perimeter plus the spanning tree's hops beyond reach (Prim's algorithm).
        let (mut x0, mut x1, mut y0, mut y1) = (f64::MAX, f64::MIN, f64::MAX, f64::MIN);
        for p in &pts {
            x0 = x0.min(p.0);
            x1 = x1.max(p.0);
            y0 = y0.min(p.1);
            y1 = y1.max(p.1);
        }
        let mut excess = 0.0;
        let k = pts.len();
        let mut in_tree = vec![false; k];
        let mut best = vec![f64::INFINITY; k];
        in_tree[0] = true;
        for j in 1..k {
            best[j] = dist(pts[0], pts[j]);
        }
        for _ in 1..k {
            let mut j = usize::MAX;
            for i in 0..k {
                if !in_tree[i] && (j == usize::MAX || best[i] < best[j]) {
                    j = i;
                }
            }
            in_tree[j] = true;
            excess += (best[j] - MAX_WIRE).max(0.0);
            for i in 0..k {
                if !in_tree[i] {
                    best[i] = best[i].min(dist(pts[j], pts[i]));
                }
            }
        }
        n.weight * ((x1 - x0) + (y1 - y0)) + 50.0 * excess
    }

    /// Pull towards the ports' corner (the origin), so that compacting pays everywhere, not
    /// only at the edges of the bounding box.
    fn gravity(&self, s: usize) -> f64 {
        let (c, r) = (s % self.slots.cols, s / self.slots.cols);
        let (x, y) = (self.slots.tile_x(c) as f64, 2.0 * r as f64);
        GRAVITY
            * match self.opts.objective {
                Objective::Area => x + y,
                Objective::MaxWidth(_) => y,
                Objective::MaxHeight(_) => x,
            }
    }

    /// The shape term: footprint, or the free side under a limit.
    fn shape(&self) -> f64 {
        let cols = self.col_count.iter().rposition(|&c| c > 0).map_or(0, |c| c + 1);
        let rows = self.row_count.iter().rposition(|&c| c > 0).map_or(0, |r| r + 1);
        let (w, h) = self.slots.tiles(cols, rows);
        match self.opts.objective {
            Objective::Area => self.frame.area(w, h) as f64,
            // Under a limit, the other side matters; the area breaks ties.
            Objective::MaxWidth(_) => h as f64 * 40.0 + (w * h) as f64 * 0.1,
            Objective::MaxHeight(_) => w as f64 * 40.0 + (w * h) as f64 * 0.1,
        }
    }

    /// Moves movable `m` to slot `s`, swapping with whatever is there.
    fn swap(&mut self, m: usize, s: usize) {
        let from = self.at[m];
        let other = self.who[s];
        let cols = self.slots.cols;
        let mv = |st: &mut Self, e: usize, a: usize, b: usize| {
            st.col_count[a % cols] -= 1;
            st.row_count[a / cols] -= 1;
            st.col_count[b % cols] += 1;
            st.row_count[b / cols] += 1;
            st.at[e] = b;
        };
        mv(self, m, from, s);
        if let Some(o) = other {
            mv(self, o, s, from);
        }
        self.who[s] = Some(m);
        self.who[from] = other;
    }

    /// The cost change of moving `m` to slot `s` (applied if `keep` says so).
    fn try_move(&mut self, m: usize, s: usize, temp: f64, rng: &mut Rng) -> bool {
        let other = self.who[s];
        let mut touched: Vec<usize> = self.nets_of[m].clone();
        if let Some(o) = other {
            touched.extend(self.nets_of[o].iter().copied());
        }
        touched.sort_unstable();
        touched.dedup();
        let from = self.at[m];
        let pull = |st: &Self| st.gravity(st.at[m]) + other.map_or(0.0, |o| st.gravity(st.at[o]));
        let before: f64 = touched.iter().map(|&j| self.net_cost[j]).sum::<f64>() + self.shape() + pull(self);
        self.swap(m, s);
        let after_nets: Vec<f64> = touched.iter().map(|&j| self.net_cost(j)).collect();
        let after = after_nets.iter().sum::<f64>() + self.shape() + pull(self);
        let delta = after - before;
        if delta <= 0.0 || rng.unit() < (-delta / temp).exp() {
            for (j, c) in touched.iter().zip(after_nets) {
                self.net_cost[*j] = c;
            }
            true
        } else {
            // Undo: put `m` back where it was (swapping `other` back too).
            self.swap(m, from);
            false
        }
    }
}

/// Places `movable` (their current positions are ignored) into a slot grid; returns the grid
/// and each entity's slot `(col, row)`. `nets` are the wire networks as member lists.
pub fn anneal(
    net: &Netlist,
    members: &[Vec<EntId>],
    movable: &[EntId],
    poles: bool,
    opts: AnnealOpts,
    frame: Frame,
    cols: Option<usize>,
) -> (Slots, Vec<(usize, usize)>) {
    let n = movable.len().max(1);
    // Grid size: room to rearrange, within any limit.
    let tile_cols = |cols: usize| Slots { cols, rows: 1, poles }.tile_x(cols.max(1) - 1) + 1;
    let slots_needed = (n as f64 * 1.05).ceil() as usize;
    let (cols, rows) = match (opts.objective, cols) {
        (Objective::Area, Some(c)) => (c.max(1), n.div_ceil(c.max(1)).max(1)),
        (Objective::Area, None) => {
            // A tight grid (with much slack the wire costs win and the entities spread out,
            // growing the footprint), shaped for the smallest whole blueprint.
            let rows_for = |c: usize| slots_needed.div_ceil(c).max(1);
            // Among shapes no more than twice as long as wide (or the squarest).
            let aspect = |c: usize| {
                let (w, h) = frame.size(tile_cols(c), 2 * rows_for(c));
                w.max(h) as f64 / w.min(h).max(1) as f64
            };
            let squarest = (1..=n).min_by(|&a, &b| aspect(a).total_cmp(&aspect(b))).unwrap_or(1);
            let c = (1..=n)
                .filter(|&c| aspect(c) <= 2.0 || c == squarest)
                .min_by_key(|&c| (frame.area(tile_cols(c), 2 * rows_for(c)), c.abs_diff(squarest)))
                .unwrap_or(1);
            (c, rows_for(c))
        }
        (Objective::MaxWidth(w), _) => {
            let mut c = 1;
            while tile_cols(c + 1) <= w as usize {
                c += 1;
            }
            (c, n.div_ceil(c) * 2 + 2)
        }
        (Objective::MaxHeight(h), _) => {
            let r = (h as usize / 2).max(1);
            (n.div_ceil(r) * 2 + 2, r)
        }
    };
    let slots = Slots { cols, rows, poles };

    let index: std::collections::HashMap<EntId, usize> = movable.iter().enumerate().map(|(i, e)| (*e, i)).collect();
    let mut nets = Vec::new();
    let mut nets_of = vec![Vec::new(); movable.len()];
    for ms in members {
        let mut mov: Vec<usize> = ms.iter().filter_map(|e| index.get(e).copied()).collect();
        mov.sort_unstable();
        mov.dedup();
        if mov.is_empty() {
            continue;
        }
        let mut fixed_ents: Vec<EntId> = ms.iter().copied().filter(|e| !index.contains_key(e)).collect();
        fixed_ents.sort_unstable();
        fixed_ents.dedup();
        let fixed = fixed_ents.iter().map(|e| net.entities[*e].pos).collect::<Vec<_>>();
        let size = mov.len() + fixed.len();
        let small = size <= SMALL;
        let j = nets.len();
        for &m in &mov {
            nets_of[m].push(j);
        }
        nets.push(Net { mov, fixed, small, weight: if small { 1.0 } else { 2.0 / size as f64 } });
    }

    // Start from the serpentine order (codegen order keeps related entities close).
    let mut at = vec![0usize; movable.len()];
    let mut who = vec![None; cols * rows];
    let mut col_count = vec![0usize; cols];
    let mut row_count = vec![0usize; rows];
    for (k, a) in at.iter_mut().enumerate() {
        let (r, j) = (k / cols, k % cols);
        let c = if r % 2 == 1 { cols - 1 - j } else { j };
        let s = r * cols + c;
        *a = s;
        who[s] = Some(k);
        col_count[c] += 1;
        row_count[r] += 1;
    }
    let mut st = State { slots: &slots, opts, frame, at, who, col_count, row_count, nets, net_cost: Vec::new(), nets_of };
    st.net_cost = (0..st.nets.len()).map(|j| st.net_cost(j)).collect();

    let mut rng = Rng(opts.seed ^ 0x5EED);
    let moves = ((n as f64) * 2000.0 * opts.effort.max(0.01)) as usize;
    // Starting temperature: typical cost changes of random moves.
    let mut sample = 0.0;
    for _ in 0..200 {
        let m = rng.below(movable.len());
        let s = rng.below(cols * rows);
        let before = st.shape() + st.nets_of[m].iter().map(|&j| st.net_cost[j]).sum::<f64>();
        let from = st.at[m];
        st.swap(m, s);
        let after = st.shape() + st.nets_of[m].iter().map(|&j| st.net_cost(j)).sum::<f64>();
        st.swap(m, from);
        sample += (after - before).abs();
    }
    // Start fairly cool: the starting order is already decent, so refine it rather than
    // scrambling it.
    let t0 = (0.1 * sample / 200.0).max(0.5);
    let t1 = 0.005;
    for i in 0..moves {
        let f = i as f64 / moves as f64;
        let temp = t0 * (t1 / t0).powf(f);
        // The move window shrinks from the whole grid to the neighbourhood.
        let reach = ((1.0 - f) * 0.5 * cols.max(rows) as f64).max(2.0) as isize;
        let m = rng.below(movable.len());
        let (c, r) = ((st.at[m] % cols) as isize, (st.at[m] / cols) as isize);
        let dc = rng.below(2 * reach as usize + 1) as isize - reach;
        let dr = rng.below(2 * reach as usize + 1) as isize - reach;
        let (nc, nr) = ((c + dc).clamp(0, cols as isize - 1), (r + dr).clamp(0, rows as isize - 1));
        let s = nr as usize * cols + nc as usize;
        if s != st.at[m] {
            st.try_move(m, s, temp, &mut rng);
        }
    }
    let placed = st.at.iter().map(|&s| (s % cols, s / cols)).collect();
    (slots, placed)
}

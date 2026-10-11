use std::cell::Cell;
use std::collections::HashMap;
use std::sync::{OnceLock, RwLock};

/// Quality levels, by index (0 = normal). With the Quality mod, each quality of a signal is a
/// separate signal on a wire.
pub const QUALITIES: [&str; 5] = ["normal", "uncommon", "rare", "epic", "legendary"];

thread_local! {
    static QUALITY_POOL: Cell<bool> = const { Cell::new(false) };
}

/// Whether internal wiring (and signal arrays) on this thread use the quality variants
/// (uncommon to legendary) of the base signals, leaving every normal signal to the program.
/// Needs the Quality mod in the game. Set by the compiler for each compilation.
pub fn set_quality_pool(on: bool) {
    QUALITY_POOL.with(|q| q.set(on));
}

pub fn quality_pool() -> bool {
    QUALITY_POOL.with(|q| q.get())
}

/// Index into the [`SignalTable`].
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Sig(pub u16);

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum SignalKind {
    Virtual,
    Item,
    Fluid,
    Recipe,
    Quality,
    SpaceLocation,
    AsteroidChunk,
}

impl SignalKind {
    pub fn as_str(self) -> &'static str {
        match self {
            SignalKind::Virtual => "virtual",
            SignalKind::Item => "item",
            SignalKind::Fluid => "fluid",
            SignalKind::Recipe => "recipe",
            SignalKind::Quality => "quality",
            SignalKind::SpaceLocation => "space-location",
            SignalKind::AsteroidChunk => "asteroid-chunk",
        }
    }

    pub fn parse(s: &str) -> Option<SignalKind> {
        Some(match s {
            "virtual" => SignalKind::Virtual,
            "item" => SignalKind::Item,
            "fluid" => SignalKind::Fluid,
            "recipe" => SignalKind::Recipe,
            "quality" => SignalKind::Quality,
            "space-location" => SignalKind::SpaceLocation,
            "asteroid-chunk" => SignalKind::AsteroidChunk,
            _ => return None,
        })
    }
}

#[derive(Clone, Debug)]
pub struct SignalInfo {
    pub kind: SignalKind,
    pub name: String,
    /// Not hidden, not a blueprint parameter, not a wildcard (each/anything/everything).
    pub usable: bool,
    /// In the base game (no expansion): the only signals used for internal wiring.
    pub base: bool,
    /// Known to the game data Ticky ships with; `false` for names a program made up (mods).
    pub known: bool,
    /// Index into [`QUALITIES`].
    pub quality: u8,
}

#[derive(Default)]
struct Inner {
    sigs: Vec<&'static SignalInfo>,
    by_key: HashMap<(SignalKind, String, u8), Sig>,
    /// First signal with each name: base game before the expansion, items before recipes.
    by_name: HashMap<String, Sig>,
}

/// Every signal the compiler knows about. One table per process: the game's own signals
/// (dumped from Factorio), plus any a program names that the game data doesn't have (mods).
pub struct SignalTable {
    inner: RwLock<Inner>,
}

const BASE_TSV: &str = include_str!("../data/signals.tsv");
const EXTRA_TSV: &str = include_str!("../data/signals-extra.tsv");

impl SignalTable {
    /// The signal table: Factorio 2.0 base game signals first, then recipes and the Space
    /// Age signals (known names, never used internally), then any interned mod signals.
    pub fn base() -> &'static SignalTable {
        static T: OnceLock<SignalTable> = OnceLock::new();
        T.get_or_init(|| {
            let t = SignalTable { inner: RwLock::new(Inner::default()) };
            t.load(BASE_TSV, true);
            t.load(EXTRA_TSV, false);
            t
        })
    }

    fn load(&self, tsv: &str, base: bool) {
        for line in tsv.lines() {
            if line.starts_with('#') || line.trim().is_empty() {
                continue;
            }
            let f: Vec<&str> = line.split('\t').collect();
            let Some(kind) = SignalKind::parse(f[0]) else { continue };
            let usable = f[2] == "false" && f[3] == "false" && f[4] == "false";
            self.add(SignalInfo { kind, name: f[1].to_string(), usable, base, known: true, quality: 0 });
        }
    }

    fn add(&self, info: SignalInfo) -> Sig {
        let mut g = self.inner.write().unwrap();
        let sig = Sig(g.sigs.len() as u16);
        g.by_key.insert((info.kind, info.name.clone(), info.quality), sig);
        if info.quality == 0 {
            // A plain name means the item (or fluid, or virtual signal) even when a modded
            // recipe of the same name was added first, e.g. by `S("x", type="recipe")`.
            let plain = |k: SignalKind| matches!(k, SignalKind::Item | SignalKind::Fluid | SignalKind::Virtual);
            match g.by_name.get(&info.name).copied() {
                None => {
                    g.by_name.insert(info.name.clone(), sig);
                }
                Some(old) if plain(info.kind) && !plain(g.sigs[old.0 as usize].kind) => {
                    g.by_name.insert(info.name.clone(), sig);
                }
                Some(_) => {}
            }
        }
        g.sigs.push(Box::leak(Box::new(info)));
        sig
    }

    /// The game's order among signals with equal values in a selector combinator (verified
    /// with the `tieprobe` scenario): items, then fluids, then virtual signals (then the other
    /// kinds), each in prototype order (the table's order), then by quality. `select` max
    /// with index 0 gives the lowest rank among the largest values; min gives the highest
    /// among the smallest.
    pub fn rank(&self, s: Sig) -> (u8, u32, u8) {
        let info = self.info(s);
        let kind = match info.kind {
            SignalKind::Item => 0,
            SignalKind::Fluid => 1,
            SignalKind::Virtual => 2,
            SignalKind::Recipe => 3,
            SignalKind::SpaceLocation => 4,
            SignalKind::AsteroidChunk => 5,
            SignalKind::Quality => 6,
        };
        let base = if info.quality == 0 { s } else { self.lookup_kind(info.kind, &info.name).unwrap_or(s) };
        (kind, base.0 as u32, info.quality)
    }

    pub fn len(&self) -> usize {
        self.inner.read().unwrap().sigs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn info(&self, s: Sig) -> &'static SignalInfo {
        self.inner.read().unwrap().sigs[s.0 as usize]
    }

    pub fn name(&self, s: Sig) -> &'static str {
        &self.info(s).name
    }

    /// The name with its quality, when not normal: `signal-A@rare`.
    pub fn display(&self, s: Sig) -> String {
        let i = self.info(s);
        match i.quality {
            0 => i.name.clone(),
            q => format!("{}@{}", i.name, QUALITIES[q as usize]),
        }
    }

    /// A signal written as `name` or `name@quality`.
    pub fn lookup_display(&self, text: &str) -> Option<Sig> {
        match text.split_once('@') {
            None => self.lookup_plain(text),
            Some((n, q)) => {
                let q = QUALITIES.iter().position(|x| *x == q)? as u8;
                Some(self.with_quality(self.lookup_plain(n)?, q))
            }
        }
    }

    /// The same signal with another quality.
    pub fn with_quality(&self, s: Sig, q: u8) -> Sig {
        let i = self.info(s);
        if i.quality == q {
            return s;
        }
        if let Some(v) = self.inner.read().unwrap().by_key.get(&(i.kind, i.name.clone(), q)).copied() {
            return v;
        }
        self.add(SignalInfo { quality: q, base: false, ..i.clone() })
    }

    /// A usable signal by exact name (any type; items win over recipes of the same name).
    pub fn lookup(&self, exact: &str) -> Option<Sig> {
        let s = *self.inner.read().unwrap().by_name.get(exact)?;
        self.info(s).usable.then_some(s)
    }

    /// A signal written without a type: [`lookup`](Self::lookup), except that a modded
    /// (unknown) signal of another type, such as a recipe from `S("x", type="recipe")`,
    /// doesn't count, and an unknown name is added as an item.
    pub fn lookup_untyped(&self, exact: &str) -> Sig {
        self.lookup_plain(exact).unwrap_or_else(|| self.intern(SignalKind::Item, exact))
    }

    /// [`lookup`](Self::lookup) for a name written without a type: a modded signal of a type
    /// other than item, fluid or virtual is only found with its type.
    pub fn lookup_plain(&self, exact: &str) -> Option<Sig> {
        self.lookup(exact).filter(|s| self.info(*s).known || matches!(self.info(*s).kind, SignalKind::Item | SignalKind::Fluid | SignalKind::Virtual))
    }

    /// A signal by type and exact name, whether or not it's usable.
    pub fn lookup_kind(&self, kind: SignalKind, exact: &str) -> Option<Sig> {
        self.inner.read().unwrap().by_key.get(&(kind, exact.to_string(), 0)).copied()
    }

    /// The signal with this type and name, adding it if the game data doesn't have it
    /// (a modded signal). Check [`SignalInfo::known`] to warn about possible typos.
    pub fn intern(&self, kind: SignalKind, exact: &str) -> Sig {
        if let Some(s) = self.lookup_kind(kind, exact) {
            return s;
        }
        self.add(SignalInfo { kind, name: exact.to_string(), usable: true, base: false, known: false, quality: 0 })
    }

    /// Resolves a signal written as a Ticky identifier: `iron_plate` → `iron-plate`,
    /// `A` → `signal-A`, `red` → `signal-red`.
    pub fn resolve_ident(&self, ident: &str) -> Option<Sig> {
        let dashed = ident.replace('_', "-");
        self.lookup_plain(&dashed).or_else(|| self.lookup_plain(&format!("signal-{dashed}")))
    }

    /// A wildcard virtual signal: `signal-each`, `signal-everything` or `signal-anything`.
    pub fn special(&self, name: &str) -> Sig {
        self.lookup_kind(SignalKind::Virtual, name).expect("wildcard signal")
    }

    /// Signals available for internal wiring, most readable first: letters, digits, colours,
    /// other virtual signals, then items and fluids. Base game only, so blueprints work
    /// with or without the expansion; with [`quality_pool`], their uncommon to legendary
    /// variants instead (four times as many, and no normal signal is used).
    pub fn internal_pool(&self) -> Vec<Sig> {
        let base = self.base_pool();
        if !quality_pool() {
            return base;
        }
        (1..QUALITIES.len() as u8).flat_map(|q| base.iter().map(move |s| (*s, q))).map(|(s, q)| self.with_quality(s, q)).collect()
    }

    fn base_pool(&self) -> Vec<Sig> {
        let rank = |i: &SignalInfo| -> u8 {
            let n = i.name.as_str();
            match i.kind {
                SignalKind::Virtual if n.len() == 8 && n.as_bytes()[7].is_ascii_uppercase() => 0,
                SignalKind::Virtual if n.len() == 8 && n.as_bytes()[7].is_ascii_digit() => 1,
                SignalKind::Virtual
                    if matches!(
                        n,
                        "signal-red" | "signal-green" | "signal-blue" | "signal-cyan" | "signal-pink"
                            | "signal-yellow" | "signal-white" | "signal-grey" | "signal-black"
                    ) =>
                {
                    2
                }
                SignalKind::Virtual => 3,
                SignalKind::Item => 4,
                SignalKind::Fluid => 5,
                _ => 6,
            }
        };
        let g = self.inner.read().unwrap();
        let mut v: Vec<Sig> = (0..g.sigs.len() as u16)
            .map(Sig)
            .filter(|s| {
                let i = g.sigs[s.0 as usize];
                i.usable && i.base && matches!(i.kind, SignalKind::Virtual | SignalKind::Item | SignalKind::Fluid)
            })
            .collect();
        v.sort_by_key(|s| (rank(g.sigs[s.0 as usize]), s.0));
        v
    }

    /// Signal arrays store element `k` on `array_signals()[k]`: the internal pool except
    /// its last signal, which [`SignalTable::index_signal`] keeps for index wires.
    pub fn array_signals(&self) -> &'static [Sig] {
        static A: [OnceLock<Vec<Sig>>; 2] = [OnceLock::new(), OnceLock::new()];
        A[quality_pool() as usize].get_or_init(|| {
            let mut p = self.internal_pool();
            p.pop();
            p
        })
    }

    /// The signal carrying an index next to an array's position table (never an element).
    pub fn index_signal(&self) -> Sig {
        static I: [OnceLock<Sig>; 2] = [OnceLock::new(), OnceLock::new()];
        *I[quality_pool() as usize].get_or_init(|| *self.internal_pool().last().unwrap())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn resolves_idents() {
        let t = SignalTable::base();
        assert_eq!(t.name(t.resolve_ident("A").unwrap()), "signal-A");
        assert_eq!(t.name(t.resolve_ident("iron_plate").unwrap()), "iron-plate");
        assert_eq!(t.name(t.resolve_ident("red").unwrap()), "signal-red");
        assert_eq!(t.name(t.resolve_ident("check").unwrap()), "signal-check");
        assert!(t.resolve_ident("each").is_none());
        assert!(t.resolve_ident("everything").is_none());
        assert_eq!(t.internal_pool().len(), 358);
        assert_eq!(t.name(t.internal_pool()[0]), "signal-A");
        assert_eq!(t.array_signals().len(), 357);
        assert!(!t.array_signals().contains(&t.index_signal()));
        // Quality variants: separate signals; the quality pool has no normal signal.
        set_quality_pool(true);
        let p = t.internal_pool();
        assert_eq!(p.len(), 358 * 4);
        assert_eq!(t.display(p[0]), "signal-A@uncommon");
        assert!(p.iter().all(|s| t.info(*s).quality > 0));
        assert_eq!(t.array_signals().len(), 358 * 4 - 1);
        assert_eq!(t.lookup_display("signal-A@uncommon"), Some(p[0]));
        assert_eq!(t.lookup("signal-A").map(|s| t.info(s).quality), Some(0));
        set_quality_pool(false);
        // Space Age names are known; items win over recipes with the same name.
        let y = t.resolve_ident("yumako").unwrap();
        assert_eq!(t.info(y).kind, SignalKind::Item);
        assert!(t.lookup_kind(SignalKind::Recipe, "iron-gear-wheel").is_some());
    }

    #[test]
    fn interns_mod_signals() {
        let t = SignalTable::base();
        let a = t.intern(SignalKind::Item, "nt-test-fuel");
        assert_eq!(t.intern(SignalKind::Item, "nt-test-fuel"), a);
        assert!(!t.info(a).known);
        let r = t.intern(SignalKind::Recipe, "nt-test-fuel");
        assert_ne!(a, r);
        assert!(!t.internal_pool().contains(&a));
    }
}

use std::collections::HashMap;
use std::sync::{OnceLock, RwLock};

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
}

#[derive(Default)]
struct Inner {
    sigs: Vec<&'static SignalInfo>,
    by_key: HashMap<(SignalKind, String), Sig>,
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
            self.add(SignalInfo { kind, name: f[1].to_string(), usable, base, known: true });
        }
    }

    fn add(&self, info: SignalInfo) -> Sig {
        let mut g = self.inner.write().unwrap();
        let sig = Sig(g.sigs.len() as u16);
        g.by_key.insert((info.kind, info.name.clone()), sig);
        g.by_name.entry(info.name.clone()).or_insert(sig);
        g.sigs.push(Box::leak(Box::new(info)));
        sig
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

    /// A usable signal by exact name (any type; items win over recipes of the same name).
    pub fn lookup(&self, exact: &str) -> Option<Sig> {
        let s = *self.inner.read().unwrap().by_name.get(exact)?;
        self.info(s).usable.then_some(s)
    }

    /// A signal by type and exact name, whether or not it's usable.
    pub fn lookup_kind(&self, kind: SignalKind, exact: &str) -> Option<Sig> {
        self.inner.read().unwrap().by_key.get(&(kind, exact.to_string())).copied()
    }

    /// The signal with this type and name, adding it if the game data doesn't have it
    /// (a modded signal). Check [`SignalInfo::known`] to warn about possible typos.
    pub fn intern(&self, kind: SignalKind, exact: &str) -> Sig {
        if let Some(s) = self.lookup_kind(kind, exact) {
            return s;
        }
        self.add(SignalInfo { kind, name: exact.to_string(), usable: true, base: false, known: false })
    }

    /// Resolves a signal written as a Ticky identifier: `iron_plate` → `iron-plate`,
    /// `A` → `signal-A`, `red` → `signal-red`.
    pub fn resolve_ident(&self, ident: &str) -> Option<Sig> {
        let dashed = ident.replace('_', "-");
        self.lookup(&dashed).or_else(|| self.lookup(&format!("signal-{dashed}")))
    }

    /// A wildcard virtual signal: `signal-each`, `signal-everything` or `signal-anything`.
    pub fn special(&self, name: &str) -> Sig {
        self.lookup_kind(SignalKind::Virtual, name).expect("wildcard signal")
    }

    /// Signals available for internal wiring, most readable first: letters, digits, colours,
    /// other virtual signals, then items and fluids. Base game only, so blueprints work
    /// with or without the expansion.
    pub fn internal_pool(&self) -> Vec<Sig> {
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

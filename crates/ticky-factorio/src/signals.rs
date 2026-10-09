use std::collections::HashMap;
use std::sync::OnceLock;

/// Index into a [`SignalTable`].
#[derive(Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct Sig(pub u16);

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum SignalKind {
    Virtual,
    Item,
    Fluid,
}

impl SignalKind {
    pub fn as_str(self) -> &'static str {
        match self {
            SignalKind::Virtual => "virtual",
            SignalKind::Item => "item",
            SignalKind::Fluid => "fluid",
        }
    }
}

#[derive(Clone, Debug)]
pub struct SignalInfo {
    pub kind: SignalKind,
    pub name: String,
    /// Not hidden, not a blueprint parameter, not a wildcard (each/anything/everything).
    pub usable: bool,
}

pub struct SignalTable {
    pub sigs: Vec<SignalInfo>,
    by_name: HashMap<String, Sig>,
}

const BASE_TSV: &str = include_str!("../data/signals.tsv");

impl SignalTable {
    /// Signals of the Factorio 2.0 base game (no Space Age), dumped from the game itself.
    pub fn base() -> &'static SignalTable {
        static T: OnceLock<SignalTable> = OnceLock::new();
        T.get_or_init(|| SignalTable::from_tsv(BASE_TSV))
    }

    fn from_tsv(tsv: &str) -> SignalTable {
        let mut sigs = Vec::new();
        let mut by_name = HashMap::new();
        for line in tsv.lines() {
            if line.starts_with('#') || line.trim().is_empty() {
                continue;
            }
            let f: Vec<&str> = line.split('\t').collect();
            let kind = match f[0] {
                "virtual" => SignalKind::Virtual,
                "item" => SignalKind::Item,
                "fluid" => SignalKind::Fluid,
                _ => continue,
            };
            let usable = f[2] == "false" && f[3] == "false" && f[4] == "false";
            let sig = Sig(sigs.len() as u16);
            // Item and fluid names never collide in the base game; virtual names are distinct too.
            by_name.entry(f[1].to_string()).or_insert(sig);
            sigs.push(SignalInfo { kind, name: f[1].to_string(), usable });
        }
        SignalTable { sigs, by_name }
    }

    pub fn len(&self) -> usize {
        self.sigs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.sigs.is_empty()
    }

    pub fn info(&self, s: Sig) -> &SignalInfo {
        &self.sigs[s.0 as usize]
    }

    pub fn name(&self, s: Sig) -> &str {
        &self.sigs[s.0 as usize].name
    }

    pub fn lookup(&self, exact: &str) -> Option<Sig> {
        self.by_name.get(exact).copied().filter(|s| self.info(*s).usable)
    }

    /// Resolves a signal written as a Ticky identifier: `iron_plate` → `iron-plate`,
    /// `A` → `signal-A`, `red` → `signal-red`.
    pub fn resolve_ident(&self, ident: &str) -> Option<Sig> {
        let dashed = ident.replace('_', "-");
        self.lookup(&dashed).or_else(|| self.lookup(&format!("signal-{dashed}")))
    }

    /// Signals available for internal wiring, most readable first: letters, digits, colours,
    /// other virtual signals, then items and fluids.
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
            }
        };
        let mut v: Vec<Sig> = (0..self.sigs.len() as u16)
            .map(Sig)
            .filter(|s| self.info(*s).usable)
            .collect();
        v.sort_by_key(|s| (rank(self.info(*s)), s.0));
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
    }
}

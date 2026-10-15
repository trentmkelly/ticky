//! Execution profiles of processes, for profile-guided optimisation (`ticky test --profile`
//! records one, `ticky build --profile` uses it).
//!
//! A profile counts, per process, how often each *raw step* ran and how often control went
//! from one raw step to the next. Raw steps are the steps `cfg::build` makes from the source
//! before any step is merged or copied (after empty jumps are threaded), numbered in the order
//! it makes them; they depend only on the source (and the optimisation mode's front end), so
//! a recompilation of the same source finds the same ones. Each is stored with its source span
//! as a check: a profile whose spans don't match the program being built is ignored with a
//! warning, as is one recorded from different source text.
//!
//! The file is JSON (from `ticky test examples/primes.ticky --profile primes.json`, cut):
//!
//! ```json
//! {
//!   "ticky_profile": 1,
//!   "source": "fnv1a64:e9071b505144d35a",
//!   "processes": [
//!     {
//!       "name": "main",
//!       "steps": [
//!         {"id":0,"span":[129,319],"line":7,"col":1,"visits":1,"branch":{"taken":1,"not_taken":0}},
//!         {"id":4,"span":[190,294],"line":10,"col":5,"visits":236,"branch":{"taken":74,"not_taken":162}},
//!         {"id":6,"span":[216,283],"line":11,"col":9,"visits":74}
//!       ],
//!       "edges": [
//!         {"from":4,"to":6,"count":74},
//!         {"from":4,"to":7,"count":162},
//!         {"from":2,"to":null,"count":1}
//!       ]
//!     }
//!   ]
//! }
//! ```
//!
//! `source` is a hash of the program text. `steps` lists every raw step (`id` = its number,
//! `span` = byte offsets of the source that made it, `line`/`col` for people); `visits` is how
//! many times it ran (summed over all the tests), and `branch` (for a step ending in a
//! two-way branch) how often the condition was true and false. `edges` are the transitions
//! that happened, `to: null` meaning the process halted. Processes are `main` and the
//! `process` names.
//!
//! Recording (testrun.rs): the simulator watches each process's program counter and commit
//! pulse ([`ticky_sim::StateTrace`]); a step of the built circuit runs one or more raw steps
//! in a row ([`crate::program::Step::origin`]), so its visits and transitions map back to raw
//! steps exactly (for a build without a profile).

use std::collections::BTreeMap;

use serde_json::{json, Value};
use ticky_syntax::{Diag, Span};

/// What a raw step is, for checking and reporting a profile (see the module docs).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RawStep {
    pub span: Span,
    /// The two targets of a branch (`None`: halt), if it ends in one.
    pub branch: Option<(Option<usize>, Option<usize>)>,
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ProcProfile {
    /// Per raw step: its span and visit count.
    pub steps: Vec<(Span, u64)>,
    /// Transitions between raw steps (`None`: halted).
    pub edges: BTreeMap<(usize, Option<usize>), u64>,
}

impl ProcProfile {
    pub fn edge(&self, from: usize, to: Option<usize>) -> u64 {
        self.edges.get(&(from, to)).copied().unwrap_or(0)
    }

    /// Whether this profile was recorded from the raw steps `raw`.
    pub fn matches(&self, raw: &[RawStep]) -> bool {
        self.steps.len() == raw.len() && self.steps.iter().zip(raw).all(|((s, _), r)| *s == r.span)
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Profile {
    /// Hash of the source text it was recorded from ([`source_hash`]).
    pub source: u64,
    /// By process name (`main` or the `process` name).
    pub procs: BTreeMap<String, ProcProfile>,
}

/// FNV-1a over the source text.
pub fn source_hash(src: &str) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for b in src.bytes() {
        h ^= b as u64;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

impl Profile {
    /// The JSON file (see the module docs). `raw` gives each process's raw steps (for
    /// branch outcomes); `src` the source (for line numbers).
    pub fn to_json(&self, raw: &BTreeMap<String, Vec<RawStep>>, src: &str) -> Value {
        let procs: Vec<Value> = self
            .procs
            .iter()
            .map(|(name, p)| {
                let steps: Vec<Value> = p
                    .steps
                    .iter()
                    .enumerate()
                    .map(|(i, (span, visits))| {
                        let (line, col) = Diag::line_col(src, span.start);
                        let mut o = json!({"id": i, "span": [span.start, span.end], "line": line, "col": col, "visits": visits});
                        if let Some((t, f)) = raw.get(name).and_then(|r| r.get(i)).and_then(|r| r.branch) {
                            o["branch"] = json!({"taken": p.edge(i, t), "not_taken": p.edge(i, f)});
                        }
                        o
                    })
                    .collect();
                let edges: Vec<Value> =
                    p.edges.iter().map(|((from, to), n)| json!({"from": from, "to": to, "count": n})).collect();
                json!({"name": name, "steps": steps, "edges": edges})
            })
            .collect();
        json!({"ticky_profile": 1, "source": format!("fnv1a64:{:016x}", self.source), "processes": procs})
    }

    /// [`Profile::to_json`] as text, one step or edge per line.
    pub fn to_text(&self, raw: &BTreeMap<String, Vec<RawStep>>, src: &str) -> String {
        let v = self.to_json(raw, src);
        let lines = |key: &str, p: &Value| -> String {
            let items: Vec<String> = p[key].as_array().unwrap().iter().map(|x| format!("        {x}")).collect();
            if items.is_empty() { "[]".into() } else { format!("[\n{}\n      ]", items.join(",\n")) }
        };
        let procs: Vec<String> = v["processes"]
            .as_array()
            .unwrap()
            .iter()
            .map(|p| format!("    {{\n      \"name\": {},\n      \"steps\": {},\n      \"edges\": {}\n    }}", p["name"], lines("steps", p), lines("edges", p)))
            .collect();
        format!("{{\n  \"ticky_profile\": 1,\n  \"source\": {},\n  \"processes\": [\n{}\n  ]\n}}\n", v["source"], procs.join(",\n"))
    }

    pub fn from_json(v: &Value) -> Result<Profile, String> {
        if v.get("ticky_profile").and_then(Value::as_u64) != Some(1) {
            return Err("not a Ticky profile (version 1)".into());
        }
        let source = v
            .get("source")
            .and_then(Value::as_str)
            .and_then(|s| s.strip_prefix("fnv1a64:"))
            .and_then(|h| u64::from_str_radix(h, 16).ok())
            .ok_or("missing or malformed `source` hash")?;
        let mut procs = BTreeMap::new();
        let bad = |what: &str| format!("malformed profile: {what}");
        for p in v.get("processes").and_then(Value::as_array).ok_or_else(|| bad("no `processes` list"))? {
            let name = p.get("name").and_then(Value::as_str).ok_or_else(|| bad("a process without a name"))?.to_string();
            let mut steps = Vec::new();
            for (i, s) in p.get("steps").and_then(Value::as_array).ok_or_else(|| bad("no `steps` list"))?.iter().enumerate() {
                if s.get("id").and_then(Value::as_u64) != Some(i as u64) {
                    return Err(bad("step ids must be 0, 1, 2, … in order"));
                }
                let span = s.get("span").and_then(Value::as_array).filter(|a| a.len() == 2);
                let span = span.and_then(|a| Some(Span::new(a[0].as_u64()? as usize, a[1].as_u64()? as usize))).ok_or_else(|| bad("a step without a `span`"))?;
                steps.push((span, s.get("visits").and_then(Value::as_u64).unwrap_or(0)));
            }
            let mut edges = BTreeMap::new();
            for e in p.get("edges").and_then(Value::as_array).ok_or_else(|| bad("no `edges` list"))? {
                let from = e.get("from").and_then(Value::as_u64).ok_or_else(|| bad("an edge without `from`"))? as usize;
                let to = match e.get("to") {
                    Some(Value::Null) | None => None,
                    Some(t) => Some(t.as_u64().ok_or_else(|| bad("an edge's `to` must be a step id or null"))? as usize),
                };
                if from >= steps.len() || to.is_some_and(|t| t >= steps.len()) {
                    return Err(bad("an edge to a step that isn't listed"));
                }
                *edges.entry((from, to)).or_insert(0) += e.get("count").and_then(Value::as_u64).unwrap_or(0);
            }
            procs.insert(name, ProcProfile { steps, edges });
        }
        Ok(Profile { source, procs })
    }
}

thread_local! {
    /// The profile guiding this compilation (set by [`crate::compile`]).
    static CURRENT: std::cell::RefCell<Option<Profile>> = const { std::cell::RefCell::new(None) };
    /// Warnings about parts of it that didn't fit the program.
    static WARNINGS: std::cell::RefCell<Vec<String>> = const { std::cell::RefCell::new(Vec::new()) };
    static GUIDE: std::cell::Cell<Guide> = const { std::cell::Cell::new(Guide { merge: false, copy: false }) };
}

/// Which profile-guided decisions a compilation makes. With neither, the profile only
/// estimates how often each step runs (the steps are those of a build without a profile).
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct Guide {
    /// If-convert hot branch targets (`cfg::merge_hot_branches`).
    pub merge: bool,
    /// Copy hot jump targets more readily, never into predecessors that didn't jump.
    pub copy: bool,
}

pub(crate) fn set_current(p: Option<Profile>, guide: Guide) {
    CURRENT.with(|c| *c.borrow_mut() = p);
    GUIDE.with(|g| g.set(guide));
}

pub(crate) fn guide() -> Guide {
    GUIDE.with(|g| g.get())
}

pub(crate) fn clear_warnings() {
    WARNINGS.with(|w| w.borrow_mut().clear());
}

/// The profile of process `name` in the current compilation, if there is one and it was
/// recorded from these raw steps (otherwise a warning is noted).
pub(crate) fn for_proc(name: &str, raw: &[RawStep]) -> Option<ProcProfile> {
    let p = CURRENT.with(|c| c.borrow().as_ref().map(|p| p.procs.get(name).cloned()))?;
    match p {
        Some(p) if p.matches(raw) => Some(p),
        Some(_) => {
            warn(format!("the profile's steps for `{name}` don't match the program (recorded from another version or --opt mode?); ignoring them"));
            None
        }
        None => None,
    }
}

pub(crate) fn warn(msg: String) {
    WARNINGS.with(|w| {
        let mut w = w.borrow_mut();
        if !w.contains(&msg) {
            w.push(msg);
        }
    });
}

pub(crate) fn take_warnings() -> Vec<Diag> {
    WARNINGS.with(|w| std::mem::take(&mut *w.borrow_mut())).into_iter().map(|m| Diag::warning(Span::default(), m)).collect()
}

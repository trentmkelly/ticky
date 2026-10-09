//! Runs a program's `test` blocks in the simulator.

use std::collections::HashMap;

use ticky_sim::Sim;
use ticky_syntax::ast::{PortDir, Stmt, StmtKind};
use ticky_syntax::{Diag, Span};

use crate::ir::{normalize, BVals, Cv, Graph, V};
use crate::lower::{self, Names};
use crate::program::Ty;
use crate::Compiled;

/// A port's value: a number, or a whole bundle.
#[derive(Clone, PartialEq, Eq, Debug)]
pub enum PVal {
    Int(i32),
    Bun(BVals),
}

impl PVal {
    fn cv(&self) -> Cv {
        match self {
            PVal::Int(k) => Cv::Int(*k),
            PVal::Bun(b) => Cv::Bun(b.clone()),
        }
    }
}

impl std::fmt::Display for PVal {
    /// Numbers as they are; bundles as `{iron-plate=5,copper-plate=3}` (no spaces).
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        match self {
            PVal::Int(k) => write!(f, "{k}"),
            PVal::Bun(b) => {
                let t = ticky_factorio::SignalTable::base();
                let parts: Vec<String> = b.iter().map(|(s, v)| format!("{}={v}", t.name(*s))).collect();
                write!(f, "{{{}}}", parts.join(","))
            }
        }
    }
}

pub struct TestOutcome {
    pub name: String,
    pub ticks: u64,
    /// `None` when the test passed.
    pub failure: Option<Diag>,
}

/// Ticks between building and turning RUN on (the same as the in-game harness).
pub const SETTLE: u64 = 30;

/// A running program in the simulator, addressed by port names.
pub struct Harness<'a> {
    pub c: &'a Compiled,
    pub sim: Sim<'a>,
    inputs: HashMap<usize, PVal>,
}

impl<'a> Harness<'a> {
    /// A simulator with the RUN switch turned on at tick 0, after the circuit has sat powered
    /// for a while (as a freshly built blueprint does, and as the in-game harness does):
    /// logic that runs regardless of RUN has settled.
    pub fn new(c: &'a Compiled) -> Self {
        let mut sim = Sim::new(&c.cg.netlist);
        sim.set_constant_on(c.cg.run_switch, false);
        for _ in 0..SETTLE {
            sim.step();
        }
        sim.tick = 0;
        sim.set_constant_on(c.cg.run_switch, true);
        Harness { c, sim, inputs: HashMap::new() }
    }

    pub fn set(&mut self, port: usize, v: PVal) {
        let p = &self.c.program.ports[port];
        let vals = match &v {
            PVal::Int(k) => vec![(p.sig, *k)],
            PVal::Bun(b) => b.clone(),
        };
        self.sim.set_external(self.c.cg.port_ents[port], vals);
        self.inputs.insert(port, v);
    }

    pub fn get(&self, port: usize) -> PVal {
        let p = &self.c.program.ports[port];
        let bundle = p.ty == Ty::Bundle;
        match p.dir {
            PortDir::Input => self.inputs.get(&port).cloned().unwrap_or(if bundle { PVal::Bun(vec![]) } else { PVal::Int(0) }),
            PortDir::Output if bundle => PVal::Bun(normalize(self.sim.outputs_of(self.c.cg.port_ents[port]).iter().copied())),
            PortDir::Output => PVal::Int(self.sim.output_of(self.c.cg.port_ents[port], p.sig)),
        }
    }

    fn snapshot(&self) -> String {
        let ports = &self.c.program.ports;
        let vals: Vec<String> = (0..ports.len()).map(|i| format!("{} = {}", ports[i].name, self.get(i))).collect();
        format!("at tick {}: {}", self.sim.tick, vals.join(", "))
    }

    fn eval(&mut self, e: &ticky_syntax::ast::Expr) -> Result<Cv, Diag> {
        struct TestNames<'b, 'c>(&'b Harness<'c>);
        impl Names for TestNames<'_, '_> {
            fn lookup(&mut self, g: &mut Graph, name: &str, span: Span) -> Result<V, Diag> {
                let h = self.0;
                if let Some(pi) = h.c.program.port_index(name) {
                    return Ok(g.cv(&h.get(pi).cv()));
                }
                if let Some(k) = h.c.program.consts.get(name) {
                    return Ok(g.cv(k));
                }
                Err(Diag::error(span, format!("tests can only read ports and constants; `{name}` is neither")))
            }
        }
        let mut g = Graph::default();
        let v = lower::expr(&mut g, &mut TestNames(self), e)?;
        Ok(g.as_cv(v).expect("test expressions are constant"))
    }

    fn eval_int(&mut self, e: &ticky_syntax::ast::Expr) -> Result<i32, Diag> {
        self.eval(e)?.int().ok_or_else(|| Diag::error(e.span, "expected a number here"))
    }

    fn exec(&mut self, s: &Stmt, src: &str) -> Result<(), Diag> {
        match &s.kind {
            StmtKind::TestSet { name, value } => {
                let pi = self
                    .c
                    .program
                    .port_index(name)
                    .filter(|&i| self.c.program.ports[i].dir == PortDir::Input)
                    .ok_or_else(|| Diag::error(s.span, format!("`{name}` is not an input port")))?;
                let v = match (self.c.program.ports[pi].ty, self.eval(value)?) {
                    (Ty::Bundle, Cv::Bun(b)) => PVal::Bun(b),
                    (Ty::Bundle, _) => return Err(Diag::error(value.span, format!("`{name}` is a bundle input; set it to a bundle"))),
                    (_, Cv::Int(k)) => PVal::Int(k),
                    _ => return Err(Diag::error(value.span, format!("`{name}` takes a number"))),
                };
                self.set(pi, v);
            }
            StmtKind::TestRun { ticks } => {
                let n = self.eval_int(ticks)?;
                for _ in 0..n.max(0) {
                    self.sim.step();
                }
            }
            StmtKind::TestRunUntil { cond, max } => {
                let max = self.eval_int(max)?.max(0);
                let mut i = 0;
                while self.eval_int(cond)? == 0 {
                    if i == max {
                        return Err(Diag::error(s.span, format!("condition still false after {max} ticks ({})", self.snapshot())));
                    }
                    self.sim.step();
                    i += 1;
                }
            }
            StmtKind::Assert(e) => {
                if self.eval_int(e)? == 0 {
                    let text = src[e.span.start..e.span.end].to_string();
                    return Err(Diag::error(s.span, format!("assertion failed: {text} ({})", self.snapshot())));
                }
            }
            StmtKind::Pass => {}
            _ => return Err(Diag::error(s.span, "tests may only use `set`, `run`, `run until` and `assert`")),
        }
        Ok(())
    }
}

pub fn run_tests(c: &Compiled, src: &str) -> Vec<TestOutcome> {
    c.program
        .tests
        .iter()
        .map(|t| {
            let mut h = Harness::new(c);
            let failure = t.body.iter().try_for_each(|s| h.exec(s, src)).err();
            TestOutcome { name: t.name.clone(), ticks: h.sim.tick, failure }
        })
        .collect()
}

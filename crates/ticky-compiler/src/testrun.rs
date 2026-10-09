//! Runs a program's `test` blocks in the simulator.

use std::collections::HashMap;

use ticky_sim::Sim;
use ticky_syntax::ast::{PortDir, Stmt, StmtKind};
use ticky_syntax::{Diag, Span};

use crate::ir::{Graph, V};
use crate::lower::{self, Names};
use crate::Compiled;

pub struct TestOutcome {
    pub name: String,
    pub ticks: u64,
    /// `None` when the test passed.
    pub failure: Option<Diag>,
}

/// A running program in the simulator, addressed by port names.
pub struct Harness<'a> {
    pub c: &'a Compiled,
    pub sim: Sim<'a>,
    inputs: HashMap<usize, i32>,
}

impl<'a> Harness<'a> {
    /// A simulator with the RUN switch turned on at tick 0.
    pub fn new(c: &'a Compiled) -> Self {
        let mut sim = Sim::new(&c.cg.netlist);
        sim.set_constant_on(c.cg.run_switch, true);
        Harness { c, sim, inputs: HashMap::new() }
    }

    pub fn set(&mut self, port: usize, v: i32) {
        self.inputs.insert(port, v);
        let p = &self.c.program.ports[port];
        self.sim.set_external(self.c.cg.port_ents[port], vec![(p.sig, v)]);
    }

    pub fn get(&self, port: usize) -> i32 {
        let p = &self.c.program.ports[port];
        match p.dir {
            PortDir::Input => self.inputs.get(&port).copied().unwrap_or(0),
            PortDir::Output => self.sim.output_of(self.c.cg.port_ents[port], p.sig),
        }
    }

    fn snapshot(&self) -> String {
        let ports = &self.c.program.ports;
        let vals: Vec<String> = (0..ports.len()).map(|i| format!("{} = {}", ports[i].name, self.get(i))).collect();
        format!("at tick {}: {}", self.sim.tick, vals.join(", "))
    }

    fn eval(&mut self, e: &ticky_syntax::ast::Expr) -> Result<i32, Diag> {
        struct TestNames<'b, 'c>(&'b Harness<'c>);
        impl Names for TestNames<'_, '_> {
            fn lookup(&mut self, g: &mut Graph, name: &str, span: Span) -> Result<V, Diag> {
                let h = self.0;
                if let Some(pi) = h.c.program.port_index(name) {
                    return Ok(g.konst(h.get(pi)));
                }
                if let Some(&k) = h.c.program.consts.get(name) {
                    return Ok(g.konst(k));
                }
                Err(Diag::error(span, format!("tests can only read ports and constants; `{name}` is neither")))
            }
        }
        let mut g = Graph::default();
        let v = lower::expr(&mut g, &mut TestNames(self), e)?;
        Ok(g.as_const(v).expect("test expressions are constant"))
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
                let v = self.eval(value)?;
                self.set(pi, v);
            }
            StmtKind::TestRun { ticks } => {
                let n = self.eval(ticks)?;
                for _ in 0..n.max(0) {
                    self.sim.step();
                }
            }
            StmtKind::TestRunUntil { cond, max } => {
                let max = self.eval(max)?.max(0);
                let mut i = 0;
                while self.eval(cond)? == 0 {
                    if i == max {
                        return Err(Diag::error(s.span, format!("condition still false after {max} ticks ({})", self.snapshot())));
                    }
                    self.sim.step();
                    i += 1;
                }
            }
            StmtKind::Assert(e) => {
                if self.eval(e)? == 0 {
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

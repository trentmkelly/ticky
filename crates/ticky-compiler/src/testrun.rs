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
                let parts: Vec<String> = b.iter().map(|(s, v)| format!("{}={v}", t.display(*s))).collect();
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
        // A control: its constant combinator changes (switched, or its value set).
        if let Some(&(_, k)) = self.c.cg.controls.iter().find(|(pi, _)| *pi == port) {
            let ctl = &self.c.program.controls.iter().find(|c| c.name == self.c.program.ports[port].name).expect("control");
            let x = match &v {
                PVal::Int(x) => *x,
                PVal::Bun(_) => 0,
            };
            if ctl.switch {
                self.sim.set_constant_on(k, x != 0);
            } else {
                self.sim.set_constant_values(k, vec![(self.c.program.ports[port].sig, x)]);
            }
            self.inputs.insert(port, v);
            return;
        }
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
        let bundle = p.ty.is_bun();
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

    /// Pixel `k` of screen `si`: what its lamp sees.
    pub fn pixel(&self, si: usize, k: usize) -> i32 {
        let lamp = self.c.cg.screen_lamps[si][k];
        match self.c.cg.netlist.entities[lamp].kind {
            ticky_factorio::netlist::Kind::Lamp(_, Some(sig)) => self.sim.net_value(lamp, ticky_factorio::netlist::Conn::Red, sig),
            ticky_factorio::netlist::Kind::Panel(ref p) => self.sim.net_value(lamp, ticky_factorio::netlist::Conn::Red, p.sig),
            ticky_factorio::netlist::Kind::Speaker(ref p) => self.sim.net_value(lamp, ticky_factorio::netlist::Conn::Red, p.sig),
            _ => unreachable!("a pixel is a colour lamp"),
        }
    }

    /// `e` with screen pixels (`screen[i]`) replaced by their values.
    fn pixels_in(&mut self, e: &ticky_syntax::ast::Expr) -> Result<ticky_syntax::ast::Expr, Diag> {
        use ticky_syntax::ast::{Expr, ExprKind};
        let mut e = e.clone();
        let mut err = None;
        fn walk(h: &mut Harness, e: &mut Expr, err: &mut Option<Diag>) {
            if let ExprKind::Index(base, idx) = &mut e.kind {
                if let ExprKind::Name(n) = &base.kind {
                    if let Some(si) = h.c.program.screens.iter().position(|s| &s.name == n && s.kind == crate::display::ScreenKind::Screen) {
                        walk(h, idx, err);
                        let n = h.c.program.screens[si].pixels();
                        match h.eval_int(idx) {
                            Ok(k) if (0..n as i32).contains(&k) => e.kind = ExprKind::Int(h.pixel(si, k as usize) as i64),
                            Ok(k) => *err = Some(Diag::error(idx.span, format!("pixel {k} is off the screen ({n} pixels)"))),
                            Err(d) => *err = Some(d),
                        }
                        return;
                    }
                }
            }
            match &mut e.kind {
                ExprKind::Unary(_, a) | ExprKind::Not(a) | ExprKind::Attr(a, _) => walk(h, a, err),
                ExprKind::Binary(_, a, b) | ExprKind::Index(a, b) => {
                    walk(h, a, err);
                    walk(h, b, err);
                }
                ExprKind::Compare(a, rest) => {
                    walk(h, a, err);
                    for (_, b) in rest {
                        walk(h, b, err);
                    }
                }
                ExprKind::BoolOp(_, xs) | ExprKind::Tuple(xs) | ExprKind::List(xs) => {
                    for x in xs {
                        walk(h, x, err);
                    }
                }
                ExprKind::IfExp { cond, then, orelse } => {
                    walk(h, cond, err);
                    walk(h, then, err);
                    walk(h, orelse, err);
                }
                ExprKind::Call { args, kwargs, .. } => {
                    for a in args {
                        walk(h, a, err);
                    }
                    for (_, a) in kwargs {
                        walk(h, a, err);
                    }
                }
                _ => {}
            }
        }
        walk(self, &mut e, &mut err);
        match err {
            Some(d) => Err(d),
            None => Ok(e),
        }
    }

    fn eval(&mut self, e: &ticky_syntax::ast::Expr) -> Result<Cv, Diag> {
        let e = &if self.c.program.screens.is_empty() { e.clone() } else { self.pixels_in(e)? };
        struct TestNames<'b, 'c>(&'b Harness<'c>);
        impl Names for TestNames<'_, '_> {
            fn lookup(&mut self, g: &mut Graph, name: &str, span: Span) -> Result<V, Diag> {
                let h = self.0;
                if let Some(pi) = h.c.program.port_index(name) {
                    let v = g.cv(&h.get(pi).cv());
                    // A Signal port's value is a signal (compare it with `S("…")`).
                    return Ok(if h.c.program.ports[pi].ty == Ty::Signal { g.sigval(v) } else { v });
                }
                if let Some(k) = h.c.program.consts.get(name) {
                    return Ok(g.cv(k));
                }
                // A panel: the value of the message it shows (0 for none).
                if let Some(si) = h.c.program.screens.iter().position(|s| s.name == name && s.kind == crate::display::ScreenKind::Panel) {
                    let v = h.pixel(si, 0);
                    let n = h.c.program.screens[si].panel.as_ref().unwrap().messages.len() as i32;
                    return Ok(g.konst(if (1..=n).contains(&v) { v } else { 0 }));
                }
                // A speaker: the value it reads (an alarm: whether it sounds; notes: the note).
                if let Some(si) = h.c.program.screens.iter().position(|s| s.name == name && s.kind == crate::display::ScreenKind::Speaker) {
                    let v = h.pixel(si, 0);
                    let alarm = h.c.program.screens[si].speaker.as_ref().is_some_and(|s| s.alert.is_some());
                    return Ok(g.konst(if alarm { (v != 0) as i32 } else { v.max(0) }));
                }
                // A readout: the number its lamps show.
                if let Some(si) = h.c.program.screens.iter().position(|s| s.name == name && s.kind == crate::display::ScreenKind::Digits) {
                    let n = crate::display::read_digits(&h.c.program.screens[si], |k| h.pixel(si, k)).map_err(|m| Diag::error(span, m))?;
                    return Ok(g.konst(n as i32));
                }
                Err(Diag::error(span, format!("tests can only read ports, readouts and constants; `{name}` is none of those")))
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
                    (Ty::Signal, Cv::Sig(sg)) => PVal::Bun(vec![(sg, 1)]),
                    (Ty::Signal, _) => return Err(Diag::error(value.span, format!("`{name}` is a Signal input; set it to a signal, e.g. S(\"iron-plate\")"))),
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

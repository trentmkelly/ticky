//! The Ticky compiler: source → analysis → IR → combinators → layout → blueprint.

pub mod bundle;
pub mod cfg;
pub mod codegen;
pub mod consteval;
pub mod expand;
pub mod fuse;
pub mod ir;
pub mod layout;
pub mod lower;
pub mod pipeline;
pub mod program;
pub mod testrun;

use serde_json::Value;
use ticky_factorio::{blueprint, Role, Sig, SignalTable};
use ticky_syntax::ast::PortDir;
use ticky_syntax::Diag;

pub use codegen::Codegen;
pub use layout::LayoutInfo;
pub use program::Program;

#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub enum Opt {
    /// Fastest circuits: `every tick:` blocks run every tick where possible.
    #[default]
    Speed,
    /// Fewest combinators: no pipelining (blocks run every few ticks instead).
    Size,
}

pub struct Options {
    /// Leave the RUN switch on in the blueprint, so the program starts as soon as it's built.
    pub autostart: bool,
    pub opt: Opt,
    /// Blueprint label.
    pub label: String,
    /// Include medium poles for power (off: the player powers it, e.g. with substations).
    /// Poles that relay long circuit wires are always included.
    pub poles: bool,
    /// Return lines: carry each output back to the west edge (north of the blueprint) on its
    /// own chain of poles.
    pub outputs_west: bool,
}

impl Default for Options {
    fn default() -> Self {
        Options { autostart: false, opt: Opt::Speed, label: String::new(), poles: true, outputs_west: false }
    }
}

pub struct Compiled {
    pub program: Program,
    pub cg: Codegen,
    pub layout: LayoutInfo,
    pub warnings: Vec<Diag>,
}

pub fn compile(src: &str, opts: &Options) -> Result<Compiled, Vec<Diag>> {
    let module = ticky_syntax::parse(src).map_err(|d| vec![d])?;
    let fast = compile_module(&module, opts, true)?;
    if opts.opt == Opt::Speed {
        return Ok(fast);
    }
    // Pipelining sometimes saves combinators (no sample registers or clocks), sometimes
    // costs them (delay chains): build both and keep the smaller.
    let slow = compile_module(&module, opts, false)?;
    let count = |c: &Compiled| c.cg.netlist.entities.iter().filter(|e| e.kind.is_combinator()).count();
    Ok(if count(&slow) < count(&fast) { slow } else { fast })
}

fn compile_module(module: &ticky_syntax::ast::Module, opts: &Options, pipeline: bool) -> Result<Compiled, Vec<Diag>> {
    let t = std::time::Instant::now();
    let mut program = program::analyze(module, pipeline)?;
    let mut cg = codegen::codegen(&program, opts.autostart).map_err(|d| vec![d])?;
    program::timing("codegen", t);
    let lo = layout::LayoutOpts { poles: opts.poles, outputs_west: opts.outputs_west };
    let layout = layout::layout(&mut cg.netlist, &cg.nets, &lo)
        .map_err(|e| vec![Diag::error(Default::default(), format!("internal layout error: {e}"))])?;
    let problems = cg.netlist.validate(opts.poles);
    if !problems.is_empty() {
        return Err(vec![Diag::error(Default::default(), format!("internal layout error: {}", problems.join("; ")))]);
    }
    let t = SignalTable::base();
    cg.netlist.label = opts.label.clone();
    let mut desc = String::from("Compiled by Ticky. Turn ON the RUN switch (the constant combinator at the top left) to start.\n");
    for p in &program.ports {
        let dir = if p.dir == PortDir::Input { "input " } else { "output" };
        if p.ty == program::Ty::Bundle {
            desc.push_str(&format!("\n{dir} {}: Bundle (every signal)", p.name));
        } else {
            desc.push_str(&format!("\n{dir} {}: {} on {}", p.name, p.ty.name(), t.name(p.sig)));
        }
    }
    cg.netlist.description = desc;
    let warnings = std::mem::take(&mut program.warnings);
    Ok(Compiled { program, cg, layout, warnings })
}

impl Compiled {
    pub fn blueprint_json(&self) -> Value {
        let t = SignalTable::base();
        let mut icons: Vec<Sig> = vec![t.lookup("decider-combinator").unwrap()];
        icons.extend(self.program.ports.iter().filter(|p| p.dir == PortDir::Output).map(|p| p.sig).take(2));
        blueprint::to_json(&self.cg.netlist, t, &icons)
    }

    pub fn blueprint_string(&self) -> String {
        blueprint::encode(&self.blueprint_json())
    }

    /// Human-readable cost report.
    pub fn report(&self, src: &str) -> String {
        let t = SignalTable::base();
        let mut out = String::new();
        for b in &self.cg.blocks {
            let (line, _) = Diag::line_col(src, b.span.start);
            let header = match b.requested {
                None => "every tick".to_string(),
                Some(n) => format!("every {n} ticks"),
            };
            let timing = match b.latency {
                Some(l) => format!("every tick (pipelined, latency {l})"),
                None => format!("period {:>3} ticks, depth {:>2}", b.period, b.depth),
            };
            out.push_str(&format!("  {header:<16} line {line:<4} {timing:<36} {:>4} combinators\n", b.combinators));
        }
        if let Some(m) = &self.cg.main {
            out.push_str(&format!("  main program     {} steps, {} combinators\n", m.steps.len(), m.combinators));
            for (i, s) in m.steps.iter().enumerate() {
                let (line, _) = Diag::line_col(src, s.span.start);
                let tag = if s.self_loop { "  (loop: per iteration)" } else { "" };
                out.push_str(&format!("    step {:<3} line {line:<4} {}{tag}\n", i + 1, s.duration));
            }
        }
        if !self.program.calls.is_empty() {
            let calls: Vec<String> = self
                .program
                .calls
                .iter()
                .map(|(f, n)| {
                    let how = if self.program.subroutines.contains(f) { "subroutine" } else { "inlined" };
                    format!("{f} ({how}, {n} call{})", if *n == 1 { "" } else { "s" })
                })
                .collect();
            out.push_str(&format!("  functions: {}\n", calls.join(", ")));
        }
        let n = &self.cg.netlist;
        let combs = n.entities.iter().filter(|e| e.kind.is_combinator()).count();
        let ports: Vec<String> = n
            .entities
            .iter()
            .filter_map(|e| match &e.role {
                Role::InputPort { name, signal } | Role::OutputPort { name, signal } => {
                    let dir = if matches!(e.role, Role::InputPort { .. }) { "in" } else { "out" };
                    let what = if t.name(*signal) == "signal-each" { "bundle" } else { t.name(*signal) };
                    Some(format!("{dir} {name} ({what})"))
                }
                _ => None,
            })
            .collect();
        out.push_str(&format!("  ports: {}\n", if ports.is_empty() { "none".into() } else { ports.join(", ") }));
        out.push_str(&format!(
            "  total: {combs} combinators, {} power poles, {} wire relays{}, {}×{} tiles, {} signals\n",
            self.layout.poles,
            self.layout.relays,
            if self.layout.carriers > 0 { format!(", {} output-line poles", self.layout.carriers) } else { String::new() },
            self.layout.width,
            self.layout.height,
            self.cg.signals_used
        ));
        out
    }
}

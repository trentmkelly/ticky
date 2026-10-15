//! The Ticky compiler: source → analysis → IR → combinators → layout → blueprint.

pub mod bundle;
pub mod cfg;
pub mod display;
pub mod codegen;
pub mod consteval;
pub mod expand;
pub mod fuse;
pub mod ir;
pub mod layout;
pub mod liveness;
pub mod lower;
pub mod pipeline;
pub mod place;
pub mod profile;
pub mod program;
pub mod stdlib;
pub mod strconst;
pub mod testrun;

use serde_json::Value;
use ticky_factorio::{blueprint, Role, Sig, SignalTable};
use ticky_syntax::ast::PortDir;
use ticky_syntax::{Diag, Span};

pub use codegen::Codegen;

thread_local! {
    static CHECKS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    static COPY_TAILS: std::cell::Cell<bool> = const { std::cell::Cell::new(true) };
    static SIZE: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Whether this compilation is `--opt=size`: set by [`compile`].
pub fn opt_size() -> bool {
    SIZE.with(|c| c.get())
}

/// Whether CFG fusion may duplicate a successor with multiple predecessors.
pub(crate) fn copy_tails() -> bool {
    COPY_TAILS.with(|c| c.get())
}

/// Whether this compilation has runtime checks (`--checks`): set by [`compile`].
pub fn checks_on() -> bool {
    CHECKS.with(|c| c.get())
}

/// Turns runtime checks on or off for compilations on this thread.
pub fn set_checks(on: bool) {
    CHECKS.with(|c| c.set(on));
}
pub use layout::LayoutInfo;
pub use program::Program;

#[derive(Copy, Clone, PartialEq, Eq, Debug, Default)]
pub enum Opt {
    /// Fastest circuits: `every tick:` blocks run every tick where possible.
    #[default]
    Speed,
    /// Fewest combinators: compare pipelining and periodic evaluation, including mixed blocks.
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
    /// Output ports on the inputs' side. With N-S ports: on the west edge, north of the
    /// blueprint (the first output northernmost), each fed by its own line of poles from a gate
    /// where the output port would be (annealed: by a gate placed like the rest). With E-W
    /// ports: in the north row, after the inputs.
    pub outputs_west: bool,
    /// With west-facing N-S outputs, put the gate at the port and omit its return buffer.
    /// This saves one combinator and one tick of output latency per port.
    pub compact_outputs: bool,
    /// Ports in rows (E-W): inputs (and `outputs_west` outputs) along the north edge, other
    /// outputs along the south edge, first port westernmost. Otherwise columns (N-S).
    pub ports_ew: bool,
    /// Experimental: place combinators by simulated annealing instead of the grid.
    pub anneal: Option<place::AnnealOpts>,
    /// Don't warn about signal names the compiler doesn't know (e.g. from mods).
    pub allow_unknown_signals: bool,
    /// Internal wiring uses the quality variants (uncommon to legendary) of signals, leaving
    /// every normal signal to the program. Needs the Quality mod (Space Age) in the game.
    pub quality: bool,
    /// Runtime checks (SPEC §13): failed `assert`s, out-of-range runtime indexes and
    /// division by zero halt the process, light the error lamp and output a code.
    pub checks: bool,
    /// Which side each screen (`import display`) goes on, by name (default north).
    pub screen_sides: Vec<(String, layout::Side)>,
    /// Item data (`items.stack_size`, …) follows Space Age rather than the base game.
    pub space_age: bool,
    /// Fixed places for peripherals by name (`--at NAME=X,Y`), overriding `at=` in the source.
    pub at: Vec<(String, (i64, i64))>,
    /// Profile-guided optimisation (`--profile`, speed mode only): processes' recorded step
    /// and branch counts (see [`profile`]). Without one, the build doesn't change.
    pub profile: Option<profile::Profile>,
}

impl Default for Options {
    fn default() -> Self {
        Options { autostart: false, opt: Opt::Speed, label: String::new(), poles: true, outputs_west: false, compact_outputs: false, ports_ew: false, anneal: None, allow_unknown_signals: false, quality: true, checks: false, screen_sides: Vec::new(), space_age: false, at: Vec::new(), profile: None }
    }
}

pub struct Compiled {
    pub program: Program,
    pub cg: Codegen,
    pub layout: LayoutInfo,
    pub warnings: Vec<Diag>,
    /// Built with quality signals inside (the game needs the Quality mod).
    pub quality: bool,
    /// Built for Space Age item data.
    pub space_age: bool,
    /// Built with a profile: estimated ticks the processes spent running steps in the
    /// profiled run, without and with profile-guided decisions.
    pub profiled: Option<(f64, f64)>,
}

pub fn compile(src: &str, opts: &Options) -> Result<Compiled, Vec<Diag>> {
    ticky_factorio::set_quality_pool(opts.quality);
    ticky_factorio::items::set_space_age(opts.space_age);
    set_checks(opts.checks);
    SIZE.with(|c| c.set(opts.opt == Opt::Size));
    COPY_TAILS.with(|c| c.set(true));
    let module = ticky_syntax::parse(src).map_err(|d| vec![d])?;
    let mut profile_warnings = Vec::new();
    let usable = opts.profile.as_ref().filter(|p| {
        let same = p.source == profile::source_hash(src);
        if !same {
            profile_warnings.push(Diag::warning(Span::default(), "the profile was recorded from a different version of this program; ignoring it"));
        } else if opts.opt == Opt::Size {
            profile_warnings.push(Diag::warning(Span::default(), "a profile only guides --opt=speed builds; ignoring it"));
        }
        same && opts.opt == Opt::Speed
    });
    let mut fast = match usable {
        None => compile_module(&module, opts, true, &[])?,
        Some(p) => {
            let r = compile_guided(&module, opts, p);
            profile_warnings.extend(profile::take_warnings());
            r?
        }
    };
    if opts.opt == Opt::Speed {
        fast.warnings.extend(profile_warnings);
        return Ok(fast);
    }
    // Preserve all four global candidates before trying mixed pipeline choices.
    // Both shared-tail duplication and pipelining can save or cost combinators.
    let count = |c: &Compiled| c.cg.netlist.entities.iter().filter(|e| e.kind.is_combinator()).count();
    let eligible: Vec<usize> = fast.program.blocks.iter().enumerate().filter_map(|(i, b)| b.pipe.as_ref().map(|_| i)).collect();
    let block_count = fast.program.blocks.len();
    let mut best = fast;
    let (mut best_copy, mut best_pipeline) = (true, true);
    for (copy, pipeline) in [(true, false), (false, true), (false, false)] {
        COPY_TAILS.with(|c| c.set(copy));
        // A speculative alternative can exceed the signal pool; keep the valid circuit.
        if let Ok(candidate) = compile_module(&module, opts, pipeline, &[]) {
            if count(&candidate) < count(&best) {
                best = candidate;
                (best_copy, best_pipeline) = (copy, pipeline);
            }
        }
    }
    COPY_TAILS.with(|c| c.set(best_copy));
    let mut choices = vec![best_pipeline; block_count];
    // A bounded coordinate search includes shared clocks/start-up/ports in the cost,
    // retaining the winning shared-tail policy. Failed alternatives leave it intact.
    if eligible.len() > 1 {
        for &bi in eligible.iter().take(8) {
            choices[bi] = !choices[bi];
            match compile_module(&module, opts, best_pipeline, &choices) {
                Ok(candidate) if count(&candidate) < count(&best) => best = candidate,
                _ => choices[bi] = !choices[bi],
            }
        }
    }
    COPY_TAILS.with(|c| c.set(true));
    best.warnings.extend(profile_warnings);
    Ok(best)
}

/// Estimated ticks the processes spent running steps in the profiled run: each step's
/// estimated runs times its duration (waits at their shortest).
fn profiled_ticks(p: &Program) -> f64 {
    use program::{StepKind, WaitN};
    p.procs
        .iter()
        .flat_map(|m| &m.steps)
        .map(|s| {
            let ticks = match &s.kind {
                StepKind::Run(_) => s.depth.max(1) + 1,
                StepKind::WaitTicks(WaitN::Const(n), _) => (*n).max(2) as u32,
                StepKind::WaitUntil(..) | StepKind::WaitTicks(WaitN::Dyn(_), _) => s.wait_ready + 2,
            };
            s.visits * ticks as f64
        })
        .sum()
}

/// A speed build guided by profile `p`: built without profile-guided decisions (exactly the
/// circuit a build without a profile makes), with all of them and with each kind alone,
/// keeping whichever has the fewest estimated ticks in the profiled run (ties: the plain one).
fn compile_guided(module: &ticky_syntax::ast::Module, opts: &Options, p: &profile::Profile) -> Result<Compiled, Vec<Diag>> {
    use profile::Guide;
    profile::clear_warnings();
    let mut best: Option<(f64, Compiled)> = None;
    let mut plain = 0.0;
    for guide in [Guide { merge: false, copy: false }, Guide { merge: true, copy: true }, Guide { merge: true, copy: false }, Guide { merge: false, copy: true }] {
        profile::set_current(Some(p.clone()), guide);
        let r = compile_module(module, opts, true, &[]);
        profile::set_current(None, Guide { merge: false, copy: false });
        let c = match r {
            Ok(c) => c,
            Err(e) if !guide.merge && !guide.copy => return Err(e),
            // A guided alternative that fails (e.g. runs out of signals) is just not taken.
            Err(_) => continue,
        };
        let ticks = profiled_ticks(&c.program);
        if best.is_none() {
            plain = ticks;
        }
        if best.as_ref().is_none_or(|(t, _)| ticks < *t) {
            best = Some((ticks, c));
        }
    }
    let (ticks, mut c) = best.expect("the plain build");
    c.profiled = Some((plain, ticks));
    Ok(c)
}

fn compile_module(module: &ticky_syntax::ast::Module, opts: &Options, pipeline: bool, choices: &[bool]) -> Result<Compiled, Vec<Diag>> {
    let t = std::time::Instant::now();
    let mut program = program::analyze_with_pipelines(module, pipeline, choices)?;
    // Gates and return lines only for N-S ports with the outputs on the west.
    if opts.compact_outputs && (!opts.outputs_west || opts.ports_ew) {
        return Err(vec![Diag::error(Default::default(), "compact outputs require --ports=ns --outputs=west")]);
    }
    let gates = opts.outputs_west && !opts.ports_ew && !opts.compact_outputs;
    let mut cg = codegen::codegen(&program, opts.autostart, gates).map_err(|d| vec![d])?;
    program::timing("codegen", t);
    let mut warnings = Vec::new();
    for (name, _) in &opts.screen_sides {
        if !program.screens.iter().any(|s| &s.name == name) {
            return Err(vec![Diag::error(Default::default(), format!("there is no screen `{name}` to place"))]);
        }
    }
    for (name, _) in &opts.at {
        if !program.screens.iter().any(|s| &s.name == name) && !program.controls.iter().any(|c| &c.name == name) {
            return Err(vec![Diag::error(Default::default(), format!("there is no peripheral `{name}` to place"))]);
        }
    }
    let at_of = |name: &str, src: Option<(i64, i64)>| opts.at.iter().find(|(n, _)| n == name).map(|x| x.1).or(src);
    let screens = program
        .screens
        .iter()
        .map(|s| {
            let side = opts.screen_sides.iter().find(|(n, _)| *n == s.name).map(|x| x.1).unwrap_or_default();
            if opts.poles && s.h > 6 {
                warnings.push(Diag::warning(
                    s.span,
                    format!("screen `{}` is {} rows tall: the poles above and below it power 3 rows each, so place substations to power the rest", s.name, s.h),
                ));
            }
            (s.w, s.h, side, at_of(&s.name, s.at))
        })
        .collect();
    let controls_at: Vec<(usize, (i64, i64))> = cg
        .controls
        .iter()
        .filter_map(|&(pi, k)| {
            let c = program.controls.iter().find(|c| c.name == program.ports[pi].name)?;
            Some((k, at_of(&c.name, c.at)?))
        })
        .collect();
    let lo = layout::LayoutOpts { poles: opts.poles, outputs_west: opts.outputs_west, ports_ew: opts.ports_ew, anneal: opts.anneal, screens, controls_at };
    // Fixed peripherals mustn't overlap each other.
    let mut fixed: Vec<(String, Span, std::collections::HashSet<(i64, i64)>)> = Vec::new();
    for (k, s) in program.screens.iter().enumerate() {
        if lo.screens[k].3.is_some() {
            let one = layout::LayoutOpts { screens: vec![lo.screens[k]], controls_at: vec![], ..lo.clone() };
            fixed.push((s.name.clone(), s.span, layout::reserved_tiles(&one)));
        }
    }
    for &(k, at) in &lo.controls_at {
        let name = cg.controls.iter().find(|c| c.1 == k).map(|c| program.ports[c.0].name.clone()).unwrap_or_default();
        let span = program.ports.iter().find(|p| p.name == name).map(|p| p.span).unwrap_or_default();
        fixed.push((name, span, [at].into_iter().collect()));
    }
    for i in 0..fixed.len() {
        for j in i + 1..fixed.len() {
            if let Some(t) = fixed[i].2.intersection(&fixed[j].2).next() {
                return Err(vec![Diag::error(fixed[j].1, format!("`{}` overlaps `{}` at ({}, {}) (with their pole rows)", fixed[j].0, fixed[i].0, t.0, t.1))
                    .with_help("move one of them with `at=(x, y)` or `--at NAME=X,Y`")]);
            }
        }
    }
    let layout = layout::layout(&mut cg.netlist, &cg.nets, &lo)
        .map_err(|e| vec![Diag::error(Default::default(), format!("internal layout error: {e}"))])?;
    let problems = cg.netlist.validate(opts.poles);
    // A fixed peripheral on the program's own ports or poles.
    if let Some(&(name, (x, y))) = problems
        .iter()
        .filter_map(|m| {
            let rest = m.strip_prefix("entities ")?;
            let (ids, at) = rest.split_once(" overlap at (")?;
            let (a, b) = ids.split_once(" and ")?;
            let (x, y) = at.trim_end_matches(')').split_once(", ")?;
            Some(((a.parse::<usize>().ok()?, b.parse::<usize>().ok()?), (x.parse::<i64>().ok()?, y.parse::<i64>().ok()?)))
        })
        .find_map(|((a, b), xy)| {
            let fixed_name = |e: usize| fixed.iter().find(|f| f.2.contains(&xy) && matches!(cg.netlist.entities[e].role, Role::Pixel { .. } | Role::Control { .. } | Role::Power)).map(|f| f.0.as_str());
            Some((fixed_name(a).or(fixed_name(b))?, xy))
        })
        .as_ref()
    {
        return Err(vec![Diag::error(Default::default(), format!("`{name}` (placed with `at=`) overlaps the program's ports or poles at ({x}, {y})"))
            .with_help("the combinator grid starts at (0, 0); the ports and RUN switch are just west of it: move it further out")]);
    }
    if !problems.is_empty() {
        // Name the entities involved.
        let named: Vec<String> = problems
            .iter()
            .map(|m| {
                let mut m = m.clone();
                for (i, e) in cg.netlist.entities.iter().enumerate().rev() {
                    m = m.replace(&format!("entity {i} "), &format!("entity {i} ({} {:?}) ", e.kind.proto_name(), e.role));
                    m = m.replace(&format!("entities {i} "), &format!("entities {i} ({} {:?}) ", e.kind.proto_name(), e.role));
                    m = m.replace(&format!("and {i} "), &format!("and {i} ({} {:?}) ", e.kind.proto_name(), e.role));
                }
                m
            })
            .collect();
        return Err(vec![Diag::error(Default::default(), format!("internal layout error: {}", named.join("; ")))]);
    }
    let t = SignalTable::base();
    cg.netlist.label = opts.label.clone();
    let mut desc = String::from("Compiled by Ticky. Turn ON the RUN switch (the constant combinator at the top left) to start.\n");
    for p in &program.ports {
        let dir = if p.dir == PortDir::Input { "input " } else { "output" };
        if p.ty == program::Ty::Bundle {
            desc.push_str(&format!("\n{dir} {}: Bundle (every signal)", p.name));
        } else if p.ty == program::Ty::Signal {
            desc.push_str(&format!("\n{dir} {}: Signal (one signal, value 1)", p.name));
        } else {
            desc.push_str(&format!("\n{dir} {}: {} on {}", p.name, p.ty.name(), t.name(p.sig)));
        }
    }
    cg.netlist.description = desc;
    warnings.extend(std::mem::take(&mut program.warnings));
    if opts.allow_unknown_signals {
        warnings.retain(|w| !w.message.starts_with("unknown signal"));
    }
    Ok(Compiled { program, cg, layout, warnings, quality: opts.quality, space_age: opts.space_age, profiled: None })
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
        for m in &self.cg.procs {
            let header = if m.name == "main" { "main program".to_string() } else { format!("process {}", m.name) };
            out.push_str(&format!("  {header:<16} {} steps, {} combinators\n", m.steps.len(), m.combinators));
            for (i, s) in m.steps.iter().enumerate() {
                let (line, _) = Diag::line_col(src, s.span.start);
                let tag = if s.self_loop { "  (loop: per iteration)" } else { "" };
                out.push_str(&format!("    step {:<3} line {line:<4} {}{tag}\n", i + 1, s.duration));
            }
        }
        if let Some((plain, guided)) = self.profiled {
            let (plain, guided) = (plain + 0.0, guided + 0.0);
            let what = if guided < plain { "profile-guided" } else { "no profile-guided changes paid off" };
            out.push_str(&format!("  profile: {what}: about {guided:.0} ticks running steps in the profiled tests ({plain:.0} without)\n"));
        }
        if !self.program.checks.is_empty() {
            out.push_str("  error codes (--checks; shown on the `error` output, signal-E):\n");
            for (i, c) in self.program.checks.iter().enumerate() {
                let (line, col) = Diag::line_col(src, c.span.start);
                out.push_str(&format!("    {:<4} line {line}:{col:<4} {} ({})\n", i + 1, c.what, c.owner));
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
                    let ty = self.program.ports.iter().find(|p| &p.name == name).map(|p| p.ty);
                    let what = match ty {
                        Some(program::Ty::Bundle) => "bundle",
                        Some(program::Ty::Signal) => "signal",
                        _ => t.name(*signal),
                    };
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

#[cfg(test)]
mod pipeline_choice_tests {
    use super::*;

    #[test]
    fn size_can_mix_pipeline_and_period_blocks() {
        let mut expr = "x".to_string();
        for k in 7..19 { expr = format!("(({expr}) * x) ^ {k}"); }
        let src = format!(r#"input stock: Bundle
input x: int @ X
input charge: int @ A
input choose: bool
input left: int
input right: int
output tail_value: int
output tail_result: int
output a: Bundle
output z: int @ Z
output steam: bool @ H
every tick:
    a = stock * 2
    z = {expr}
every tick:
    if charge < 20:
        steam = True
    elif charge > 80:
        steam = False

if choose:
    wait 5
    tail_value = left
else:
    wait 7
    tail_value = right
tail_result = (((tail_value * 73) ^ (tail_value >> 3)) * 91) ^ ((tail_value * 127) >> 7)

test "mixed blocks":
    set choose = 1
    set left = 123
    set right = 456
    set stock = Bundle(iron_plate=3)
    set x = 1
    set charge = 10
    run 90 ticks
    assert a == Bundle(iron_plate=6) and z == 21 and steam
    assert tail_value == 123
    assert tail_result == (((123 * 73) ^ (123 >> 3)) * 91) ^ ((123 * 127) >> 7)
    set charge = 90
    run 10 ticks
    assert not steam
"#);
        let opts = Options { opt: Opt::Size, ..Default::default() };
        let chosen = compile(&src, &opts).unwrap();
        assert!(copy_tails(), "speculative size choices must not leak into the next compilation");
        let module = ticky_syntax::parse(&src).unwrap();
        let count = |c: &Compiled| c.cg.netlist.entities.iter().filter(|e| e.kind.is_combinator()).count();
        let mut smallest_global = usize::MAX;
        for copy in [true, false] {
            COPY_TAILS.with(|c| c.set(copy));
            for pipeline in [true, false] {
                let endpoint = compile_module(&module, &opts, pipeline, &[]).unwrap();
                smallest_global = smallest_global.min(count(&endpoint));
            }
        }
        COPY_TAILS.with(|c| c.set(true));
        assert!(count(&chosen) < smallest_global);
        assert!(chosen.program.blocks[0].pipe.is_none());
        assert!(chosen.program.blocks[1].pipe.is_some());
        assert!(chosen.cg.netlist.validate(true).is_empty());
        for r in crate::testrun::run_tests(&chosen, &src) { assert!(r.failure.is_none(), "{:?}", r.failure); }
    }
}

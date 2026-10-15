use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use ticky_compiler::program::Ty;
use ticky_compiler::testrun::{raw_steps, run_tests, run_tests_profiled, Harness, PVal};
use ticky_compiler::{compile, Compiled, Opt, Options};
use ticky_factorio::{blueprint, SignalTable, QUALITIES};
use ticky_syntax::ast::PortDir;
use ticky_syntax::{Diag, Severity};

#[derive(Parser)]
#[command(name = "ticky", version, about = "Compile Ticky programs into Factorio 2.0 blueprints")]
struct Cli {
    #[command(subcommand)]
    cmd: Cmd,
}

#[derive(Subcommand)]
enum Cmd {
    /// Compile to a blueprint string.
    Build {
        file: PathBuf,
        /// Output file (default: stdout).
        #[arg(short, long)]
        output: Option<PathBuf>,
        /// Write blueprint JSON instead of a blueprint string.
        #[arg(long)]
        json: bool,
        /// Save the RUN switch as on, so the program starts as soon as it's built.
        #[arg(long)]
        autostart: bool,
        /// Optimise for `speed` (default) or `size`.
        #[arg(long, default_value = "speed", value_parser = parse_opt)]
        opt: Opt,
        #[command(flatten)]
        place: Placement,
    },
    /// Check a program and print its cost report.
    Check {
        file: PathBuf,
        #[arg(long, default_value = "speed", value_parser = parse_opt)]
        opt: Opt,
        #[command(flatten)]
        place: Placement,
    },
    /// Run the program's `test` blocks in the simulator.
    Test {
        file: PathBuf,
        /// Optimisation mode, as for `build` (the circuit tested is the one that mode builds).
        #[arg(long, default_value = "speed", value_parser = parse_opt)]
        opt: Opt,
        /// Don't warn about signal names Ticky doesn't know (modded names).
        #[arg(long)]
        allow_unknown_signals: bool,
        /// Compile with runtime checks (see `build --checks`).
        #[arg(long)]
        checks: bool,
        /// Item data for Space Age (see `build --space-age`).
        #[arg(long)]
        space_age: bool,
        /// Record a profile while the tests run: how often each step of every process ran
        /// and which way its branches went (JSON), for `ticky build --profile FILE` (record
        /// it with the options you build with; profiles guide `--opt=speed` builds).
        #[arg(long, value_name = "FILE")]
        profile: Option<PathBuf>,
        /// Test the circuit `build --profile FILE` makes (can't be combined with --profile).
        #[arg(long, value_name = "FILE", conflicts_with = "profile")]
        use_profile: Option<PathBuf>,
    },
    /// Simulate and print output ports whenever they change.
    Sim {
        file: PathBuf,
        /// Optimisation mode, as for `build` (the circuit tested is the one that mode builds).
        #[arg(long, default_value = "speed", value_parser = parse_opt)]
        opt: Opt,
        #[arg(long, default_value_t = 600)]
        ticks: u64,
        /// Set an input: `name=value` (at tick 0) or `name=value@tick`. Repeatable.
        /// `RUN=0@tick` / `RUN=1@tick` switch the program off and on.
        #[arg(long = "set")]
        sets: Vec<String>,
        /// Print every tick instead of only changes.
        #[arg(long)]
        all: bool,
        /// Don't warn about signal names Ticky doesn't know (modded names).
        #[arg(long)]
        allow_unknown_signals: bool,
        /// Compile with runtime checks (see `build --checks`).
        #[arg(long)]
        checks: bool,
        /// Item data for Space Age (see `build --space-age`).
        #[arg(long)]
        space_age: bool,
        /// Simulate the circuit `build --profile FILE` makes.
        #[arg(long, value_name = "FILE")]
        profile: Option<PathBuf>,
    },
    /// Run the program in the simulator and in headless Factorio, and compare tick by tick.
    Difftest {
        file: PathBuf,
        #[arg(long, default_value_t = 300)]
        ticks: u64,
        #[arg(long = "set")]
        sets: Vec<String>,
        #[command(flatten)]
        place: Placement,
    },
    /// Decode a blueprint string (from a file or argument) to JSON.
    Decode { input: String },
}

/// Where the blueprint's pieces go.
#[derive(clap::Args, Clone)]
struct Placement {
    /// Leave out the medium poles that power the combinators (power them yourself, e.g.
    /// with substations). Poles that carry long circuit wires stay.
    #[arg(long)]
    no_poles: bool,
    /// How the ports are lined up: `ns` (default) in columns down the west (inputs) and east
    /// (outputs) edges, or `ew` in rows along the north (inputs) and south (outputs) edges,
    /// first port westernmost.
    #[arg(long, default_value = "ns", value_parser = ["ns", "ew"])]
    ports: String,
    /// Which edge the output ports are on. With `--ports=ns`: `east` (default) or `west` (north
    /// of the blueprint at the west edge, the first output northernmost, each fed by its own
    /// line of poles from a gate on the east edge; with `--place=anneal`, by a gate placed like
    /// the other combinators; without return lines, as with `--place=anneal` or
    /// `--compact-outputs`, under the inputs instead). With `--ports=ew`: `south` (default) or `north` (in the north
    /// row, after the inputs).
    #[arg(long, value_parser = parse_side)]
    outputs: Option<Side>,
    /// With --ports=ns --outputs=west, move each gate to its port, saving one combinator
    /// and one tick of output latency. The default keeps the existing return buffers.
    #[arg(long)]
    compact_outputs: bool,
    /// How to place the combinators: `grid` (default) or `anneal` (experimental: simulated
    /// annealing for a smaller footprint).
    #[arg(long, default_value = "grid", value_parser = ["grid", "anneal"])]
    place: String,
    /// With `--place=anneal`: the layout may be at most this many tiles wide (and as short
    /// as possible).
    #[arg(long)]
    max_width: Option<u32>,
    /// With `--place=anneal`: at most this many tiles tall (and as narrow as possible).
    #[arg(long)]
    max_height: Option<u32>,
    /// With `--place=anneal`: random seed (same seed, same layout).
    #[arg(long, default_value_t = 1)]
    seed: u64,
    /// With `--place=anneal`: how hard to try (1 = default; more is slower and usually better).
    #[arg(long, default_value_t = 1.0)]
    effort: f64,
    /// Don't warn about item/recipe/signal names Ticky doesn't know (modded names).
    #[arg(long)]
    allow_unknown_signals: bool,
    /// Don't use quality signals (uncommon to legendary) for internal wiring, for games
    /// without the Quality mod (Space Age). Internal wiring then uses normal signals.
    #[arg(long)]
    no_quality: bool,
    /// Runtime checks: failed `assert`s, out-of-range runtime indexes and division by zero
    /// halt the process, light the error lamp and put a code on the `error` output (signal-E).
    #[arg(long)]
    checks: bool,
    /// Item data (`items.stack_size`, `items.rocket_capacity`) as in Space Age rather than
    /// the base game (a few items differ).
    #[arg(long)]
    space_age: bool,
    /// Where a screen (`import display`) goes: `NAME=north` (default), `south`, `east` or
    /// `west` of the rest of the blueprint. Repeat for several screens.
    #[arg(long = "display", value_parser = parse_display)]
    displays: Vec<(String, Side)>,
    /// Put a peripheral (screen, readout, panel, speaker or control) at a fixed place:
    /// `NAME=X,Y`, its top-left tile counted from the top-left corner of the combinator grid
    /// (the ports and RUN switch are just west of it). Overrides `at=` in the program.
    #[arg(long = "at", value_parser = parse_at)]
    at: Vec<(String, (i64, i64))>,
    /// Profile-guided optimisation: a profile written by `ticky test --profile FILE`. Steps
    /// and branches the tests ran often get fewer ticks (spending combinators where that pays
    /// off), ones they never ran stay compact. `--opt=speed` only; without it the build is
    /// unchanged.
    #[arg(long, value_name = "FILE")]
    profile: Option<PathBuf>,
}

fn parse_at(s: &str) -> Result<(String, (i64, i64)), String> {
    let usage = "expected NAME=X,Y, e.g. `screen=0,10`";
    let (name, xy) = s.split_once('=').ok_or(usage)?;
    let (x, y) = xy.split_once(',').ok_or(usage)?;
    Ok((name.to_string(), (x.trim().parse().map_err(|_| usage)?, y.trim().parse().map_err(|_| usage)?)))
}

fn parse_display(s: &str) -> Result<(String, Side), String> {
    let (name, side) = s.split_once('=').ok_or("expected NAME=SIDE, e.g. `screen=east`")?;
    Ok((name.to_string(), parse_side(side)?))
}

impl Placement {
    fn anneal(&self) -> Option<ticky_compiler::place::AnnealOpts> {
        use ticky_compiler::place::{AnnealOpts, Objective};
        if self.place != "anneal" {
            return None;
        }
        let objective = match (self.max_width, self.max_height) {
            (Some(w), _) => Objective::MaxWidth(w),
            (None, Some(h)) => Objective::MaxHeight(h),
            (None, None) => Objective::Area,
        };
        Some(AnnealOpts { objective, seed: self.seed, effort: self.effort })
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Side {
    East,
    West,
    North,
    South,
}

fn parse_side(s: &str) -> Result<Side, String> {
    match s {
        "east" => Ok(Side::East),
        "west" => Ok(Side::West),
        "north" => Ok(Side::North),
        "south" => Ok(Side::South),
        _ => Err("expected `east`, `west`, `north` or `south`".into()),
    }
}

impl Placement {
    /// (ports in rows, outputs on the inputs' side), checking that the sides fit the axis.
    fn port_layout(&self) -> Result<(bool, bool), String> {
        let ew = self.ports == "ew";
        match (ew, self.outputs) {
            (false, None | Some(Side::East)) => Ok((false, false)),
            (false, Some(Side::West)) => Ok((false, true)),
            (true, None | Some(Side::South)) => Ok((true, false)),
            (true, Some(Side::North)) => Ok((true, true)),
            (false, _) => Err("with `--ports=ns`, outputs go `east` or `west`".into()),
            (true, _) => Err("with `--ports=ew`, outputs go `south` or `north`".into()),
        }
    }
}

fn parse_opt(s: &str) -> Result<Opt, String> {
    match s {
        "speed" => Ok(Opt::Speed),
        "size" => Ok(Opt::Size),
        _ => Err("expected `speed` or `size`".into()),
    }
}

fn load(file: &Path) -> Result<(String, String), ExitCode> {
    match std::fs::read_to_string(file) {
        Ok(s) => Ok((file.display().to_string(), s)),
        Err(e) => {
            eprintln!("error: can't read {}: {e}", file.display());
            Err(ExitCode::FAILURE)
        }
    }
}

fn load_profile(p: &Path) -> Result<ticky_compiler::profile::Profile, String> {
    let text = std::fs::read_to_string(p).map_err(|e| format!("can't read the profile: {e}"))?;
    let v: serde_json::Value = serde_json::from_str(&text).map_err(|e| format!("not JSON: {e}"))?;
    ticky_compiler::profile::Profile::from_json(&v)
}

fn print_diags(diags: &[Diag], file: &str, src: &str) {
    for d in diags {
        eprint!("{}", d.render(file, src));
    }
}

fn build(file: &Path, autostart: bool, opt: Opt, place: &Placement) -> Result<(String, String, Compiled), ExitCode> {
    let (name, src) = load(file)?;
    let label = file.file_stem().map(|s| s.to_string_lossy().to_string()).unwrap_or_default();
    let (ports_ew, outputs_west) = place.port_layout().map_err(|e| {
        eprintln!("error: {e}");
        ExitCode::FAILURE
    })?;
    let screen_sides = place
        .displays
        .iter()
        .map(|(n, s)| {
            let side = match s {
                Side::North => ticky_compiler::layout::Side::North,
                Side::South => ticky_compiler::layout::Side::South,
                Side::East => ticky_compiler::layout::Side::East,
                Side::West => ticky_compiler::layout::Side::West,
            };
            (n.clone(), side)
        })
        .collect();
    let profile = match &place.profile {
        None => None,
        Some(p) => Some(load_profile(p).map_err(|e| {
            eprintln!("error: {}: {e}", p.display());
            ExitCode::FAILURE
        })?),
    };
    let opts = Options { autostart, label, opt, poles: !place.no_poles, outputs_west, compact_outputs: place.compact_outputs, ports_ew, anneal: place.anneal(), allow_unknown_signals: place.allow_unknown_signals, quality: !place.no_quality, checks: place.checks, screen_sides, space_age: place.space_age, at: place.at.clone(), profile };
    match compile(&src, &opts) {
        Ok(c) => {
            print_diags(&c.warnings, &name, &src);
            Ok((name, src, c))
        }
        Err(diags) => {
            print_diags(&diags, &name, &src);
            let n = diags.iter().filter(|d| d.severity == Severity::Error).count();
            eprintln!("{n} error(s)");
            Err(ExitCode::FAILURE)
        }
    }
}

/// Parses a bundle value: `iron-plate:5,copper-plate:3` (or `name=value`; `{}` is empty).
fn parse_bundle(val: &str) -> Result<PVal, String> {
    let t = SignalTable::base();
    let mut vals = Vec::new();
    for part in val.trim_matches(|c| c == '{' || c == '}').split(',').filter(|p| !p.trim().is_empty()) {
        let (n, v) = part.rsplit_once([':', '=']).ok_or(format!("expected signal:value in `{part}`"))?;
        let n = n.trim();
        let sig = t
            .lookup_display(n)
            .or_else(|| t.resolve_ident(n))
            .unwrap_or_else(|| t.intern(ticky_factorio::SignalKind::Item, n));
        vals.push((sig, v.trim().parse::<i32>().map_err(|e| format!("bad value in `{part}`: {e}"))?));
    }
    Ok(PVal::Bun(ticky_compiler::ir::normalize(vals)))
}

/// Parses `name=value[@tick]` into (tick, port index, value).
fn parse_sets(c: &Compiled, sets: &[String]) -> Result<Vec<(u64, usize, PVal)>, String> {
    let mut out = Vec::new();
    for s in sets {
        let (name, rest) = s.split_once('=').ok_or(format!("expected name=value, got `{s}`"))?;
        // `@tick` at the end (a bundle's signals may have `@quality` too).
        let (val, tick) = match rest.rsplit_once('@') {
            Some((v, t)) if t.bytes().all(|c| c.is_ascii_digit()) => (v, t.parse::<u64>().map_err(|e| format!("bad tick in `{s}`: {e}"))?),
            _ => (rest, 0),
        };
        let int = |val: &str| -> Result<i32, String> {
            match val {
                "True" | "true" => Ok(1),
                "False" | "false" => Ok(0),
                _ => val.parse::<i32>().map_err(|e| format!("bad value in `{s}`: {e}")),
            }
        };
        // `RUN` toggles the RUN switch.
        if name == "RUN" {
            out.push((tick, usize::MAX, PVal::Int(int(val)?)));
            continue;
        }
        let pi = c
            .program
            .port_index(name)
            .filter(|&i| c.program.ports[i].dir == PortDir::Input)
            .ok_or(format!("`{name}` is not an input port"))?;
        let v = match c.program.ports[pi].ty {
            Ty::Bundle => parse_bundle(val)?,
            // A Signal input: `name` (that signal = 1), or a bundle.
            Ty::Signal if !val.contains([':', '=']) && !val.starts_with('{') => parse_bundle(&format!("{val}:1"))?,
            Ty::Signal => parse_bundle(val)?,
            _ => PVal::Int(int(val)?),
        };
        out.push((tick, pi, v));
    }
    out.sort_by_key(|s| s.0);
    Ok(out)
}

/// A value as the harness writes it: numbers, or `{name=value,…}` sorted by signal name.
fn canonical(v: &PVal) -> String {
    match v {
        PVal::Int(k) => k.to_string(),
        PVal::Bun(b) => {
            let t = SignalTable::base();
            let mut parts: Vec<(String, i32)> = b.iter().map(|(s, v)| (t.display(*s), *v)).collect();
            parts.sort();
            let parts: Vec<String> = parts.iter().map(|(n, v)| format!("{n}={v}")).collect();
            format!("{{{}}}", parts.join(","))
        }
    }
}

/// Output values observed at each tick, after applying that tick's input changes.
fn sim_trace(c: &Compiled, sets: &[(u64, usize, PVal)], ticks: u64) -> Vec<Vec<PVal>> {
    let outs: Vec<usize> = (0..c.program.ports.len()).filter(|&i| c.program.ports[i].dir == PortDir::Output).collect();
    let mut h = Harness::new(c);
    let mut rows = Vec::new();
    for i in 0..ticks {
        for (_, pi, v) in sets.iter().filter(|s| s.0 == i) {
            if *pi == usize::MAX {
                h.sim.set_constant_on(c.cg.run_switch, *v != PVal::Int(0));
            } else {
                h.set(*pi, v.clone());
            }
        }
        rows.push(outs.iter().map(|&o| h.get(o)).collect());
        h.sim.step();
    }
    rows
}

/// Each screen's pixels at each tick, as the harness writes them: the colours shown
/// (`value & 0xFFFFFF`, 0 while a lamp is off), comma-separated. Calibrated in-game: outputs
/// are read as of the tick before, a lamp's colour as of the current tick, and whether it's on
/// from the tick before that; so row `i` shows the colour at `i + 1` if the pixel was nonzero
/// at `i`.
fn screen_trace(c: &Compiled, sets: &[(u64, usize, PVal)], ticks: u64) -> Vec<Vec<String>> {
    let mut h = Harness::new(c);
    let read = |h: &Harness| -> Vec<Vec<i32>> {
        c.program.screens.iter().enumerate().map(|(si, s)| (0..s.pixels()).map(|k| h.pixel(si, k)).collect()).collect()
    };
    let mut rows = Vec::new();
    for i in 0..ticks {
        for (_, pi, v) in sets.iter().filter(|s| s.0 == i) {
            if *pi == usize::MAX {
                h.sim.set_constant_on(c.cg.run_switch, *v != PVal::Int(0));
            } else {
                h.set(*pi, v.clone());
            }
        }
        let on = read(&h);
        h.sim.step();
        let now = read(&h);
        rows.push(
            on.iter()
                .zip(&now)
                .zip(&c.program.screens)
                .map(|((on, now), sc)| match (&sc.panel, &sc.speaker) {
                    // A panel: the message it shows (as of the tick before).
                    (Some(p), _) => (if (1..=p.messages.len() as i32).contains(&on[0]) { on[0] } else { 0 }).to_string(),
                    // A speaker: the value on its wire while its condition holds (both read
                    // as of this tick), else 0.
                    (_, Some(s)) => (if (s.alert.is_some() && now[0] != 0) || now[0] > 0 { now[0] } else { 0 }).to_string(),
                    _ => on.iter().zip(now).map(|(o, v)| if *o != 0 { (v & 0xFF_FFFF).to_string() } else { "0".into() }).collect::<Vec<_>>().join(","),
                })
                .collect(),
        );
    }
    rows
}

fn harness_dir() -> PathBuf {
    std::env::var_os("TICKY_HARNESS")
        .map(PathBuf::from)
        .unwrap_or_else(|| Path::new(env!("CARGO_MANIFEST_DIR")).join("../../harness"))
}

fn lua_str(s: &str) -> String {
    serde_json::to_string(s).unwrap()
}

/// A Lua job file for the in-game harness (harness/ticky-harness).
fn job_lua(c: &Compiled, sets: &[(u64, usize, PVal)], ticks: u64) -> String {
    let t = SignalTable::base();
    let sig = |s| {
        let info = t.info(s);
        format!("{{type={}, name={}, quality={}}}", lua_str(info.kind.as_str()), lua_str(&info.name), lua_str(QUALITIES[info.quality as usize]))
    };
    let mut ports = Vec::new();
    for (i, p) in c.program.ports.iter().enumerate() {
        // A control: the constant combinator the harness switches or edits.
        let control = match c.cg.controls.iter().find(|(pi, _)| *pi == i) {
            Some(&(_, k)) => {
                let switch = c.program.controls.iter().any(|x| x.name == p.name && x.switch);
                format!(", control={}, switch={switch}", k + 1)
            }
            None => String::new(),
        };
        ports.push(format!(
            "{{name={}, dir={}, entity={}, signal={}, bundle={}{control}}}",
            lua_str(&p.name),
            lua_str(if p.dir == PortDir::Input { "in" } else { "out" }),
            c.cg.port_ents[i] + 1,
            sig(p.sig),
            p.ty.is_bun()
        ));
    }
    let sets: Vec<String> = sets
        .iter()
        .map(|(tk, pi, v)| match v {
            PVal::Int(k) => format!("{{t={tk}, port={}, value={k}}}", pi.wrapping_add(1)),
            PVal::Bun(b) => {
                let vals: Vec<String> = b
                    .iter()
                    .map(|(s, k)| {
                        let info = t.info(*s);
                        let q = lua_str(QUALITIES[info.quality as usize]);
                        format!("{{type={}, name={}, quality={q}, value={k}}}", lua_str(info.kind.as_str()), lua_str(&info.name))
                    })
                    .collect();
                format!("{{t={tk}, port={}, values={{{}}}}}", pi + 1, vals.join(", "))
            }
        })
        .collect();
    let screens: Vec<String> = c
        .cg
        .screen_lamps
        .iter()
        .map(|lamps| format!("{{{}}}", lamps.iter().map(|e| (e + 1).to_string()).collect::<Vec<_>>().join(",")))
        .collect();
    format!(
        "return {{\n  bp = {},\n  ticks = {ticks},\n  run = {},\n  ports = {{{}}},\n  sets = {{{}}},\n  screens = {{{}}},\n}}\n",
        lua_str(&c.blueprint_string()),
        c.cg.run_switch + 1,
        ports.join(", "),
        sets.join(", "),
        screens.join(", ")
    )
}

fn default_place() -> Placement {
    Placement { no_poles: false, ports: "ns".into(), outputs: None, compact_outputs: false, place: "grid".into(), max_width: None, max_height: None, seed: 1, effort: 1.0, allow_unknown_signals: false, no_quality: false, checks: false, displays: Vec::new(), space_age: false, at: Vec::new(), profile: None }
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    let res = match cli.cmd {
        Cmd::Build { file, output, json, autostart, opt, place } => build(&file, autostart, opt, &place).and_then(|(_, src, c)| {
            eprint!("{}", c.report(&src));
            let text = if json {
                serde_json::to_string_pretty(&c.blueprint_json()).unwrap()
            } else {
                c.blueprint_string()
            };
            match output {
                Some(p) => std::fs::write(&p, text + "\n").map_err(|e| {
                    eprintln!("error: can't write {}: {e}", p.display());
                    ExitCode::FAILURE
                }),
                None => {
                    println!("{text}");
                    Ok(())
                }
            }
        }),
        Cmd::Check { file, opt, place } => build(&file, false, opt, &place).map(|(_, src, c)| eprint!("{}", c.report(&src))),
        Cmd::Test { file, opt, allow_unknown_signals, checks, space_age, profile, use_profile } => build(&file, false, opt, &Placement { allow_unknown_signals, checks, space_age, profile: use_profile, ..default_place() }).and_then(|(name, src, c)| {
            let results = match &profile {
                None => run_tests(&c, &src),
                Some(out) => {
                    let (results, prof) = run_tests_profiled(&c, &src);
                    std::fs::write(out, prof.to_text(&raw_steps(&c), &src)).map_err(|e| {
                        eprintln!("error: can't write {}: {e}", out.display());
                        ExitCode::FAILURE
                    })?;
                    eprintln!("profile written to {}", out.display());
                    results
                }
            };
            if results.is_empty() {
                eprintln!("no tests in {name}");
            }
            let mut failed = 0;
            for r in &results {
                match &r.failure {
                    None => eprintln!("test {} ... ok ({} ticks)", r.name, r.ticks),
                    Some(d) => {
                        failed += 1;
                        eprintln!("test {} ... FAILED", r.name);
                        eprint!("{}", d.render(&name, &src));
                    }
                }
            }
            eprintln!("{} passed, {failed} failed", results.len() - failed);
            if failed > 0 {
                Err(ExitCode::FAILURE)
            } else {
                Ok(())
            }
        }),
        Cmd::Sim { file, opt, ticks, sets, all, allow_unknown_signals, checks, space_age, profile } => build(&file, false, opt, &Placement { allow_unknown_signals, checks, space_age, profile, ..default_place() }).and_then(|(_, _, c)| {
            let sets = parse_sets(&c, &sets).map_err(|e| {
                eprintln!("error: {e}");
                ExitCode::FAILURE
            })?;
            let names: Vec<&str> =
                c.program.ports.iter().filter(|p| p.dir == PortDir::Output).map(|p| p.name.as_str()).collect();
            println!("tick  {}", names.join("  "));
            let rows = sim_trace(&c, &sets, ticks);
            for (i, row) in rows.iter().enumerate() {
                if all || i == 0 || rows[i - 1] != *row {
                    let cells: Vec<String> = row.iter().zip(&names).map(|(v, n)| format!("{:>w$}", v.to_string(), w = n.len())).collect();
                    println!("{i:>4}  {}", cells.join("  "));
                }
            }
            Ok(())
        }),
        Cmd::Difftest { file, ticks, sets, place } => build(&file, false, Opt::Speed, &Placement { no_poles: false, ..place }).and_then(|(_, _, c)| {
            let sets = parse_sets(&c, &sets).map_err(|e| {
                eprintln!("error: {e}");
                ExitCode::FAILURE
            })?;
            let expected = sim_trace(&c, &sets, ticks);
            let job = std::env::temp_dir().join("ticky-job.lua");
            std::fs::write(&job, job_lua(&c, &sets, ticks)).unwrap();
            let script = harness_dir().join("run.sh");
            let mut cmd = std::process::Command::new(&script);
            if c.quality {
                cmd.env("TICKY_QUALITY", "1");
            }
            if c.space_age {
                cmd.env("TICKY_SPACE_AGE", "1");
            }
            let status = cmd.arg(&job).status();
            if !matches!(status, Ok(s) if s.success()) {
                eprintln!("error: harness failed ({})", script.display());
                return Err(ExitCode::FAILURE);
            }
            let trace = std::fs::read_to_string("/tmp/ticky-harness/script-output/ticky/trace.txt").map_err(|e| {
                eprintln!("error: no trace from the game: {e}");
                ExitCode::FAILURE
            })?;
            let mut expected: Vec<Vec<String>> = expected.iter().map(|r| r.iter().map(canonical).collect()).collect();
            // Screens: every pixel's colour as shown (0 while off), one column per screen.
            for (row, px) in expected.iter_mut().zip(screen_trace(&c, &sets, ticks)) {
                row.extend(px);
            }
            let mut actual: Vec<Vec<String>> =
                trace.lines().map(|l| l.split_whitespace().skip(1).map(|v| v.to_string()).collect()).collect();
            // Values that depend on random picks can't match: compared as `*`.
            let cols: Vec<&str> = c
                .program
                .ports
                .iter()
                .filter(|p| p.dir == PortDir::Output)
                .map(|p| p.name.as_str())
                .chain(c.program.screens.iter().map(|s| s.name.as_str()))
                .collect();
            let skip: Vec<usize> = cols.iter().enumerate().filter(|(_, n)| c.program.random.contains(**n)).map(|(i, _)| i).collect();
            if !skip.is_empty() {
                let names: Vec<&str> = skip.iter().map(|&i| cols[i]).collect();
                eprintln!("not compared (random): {}", names.join(", "));
                for row in expected.iter_mut().chain(actual.iter_mut()) {
                    for &i in &skip {
                        if let Some(x) = row.get_mut(i) {
                            *x = "*".into();
                        }
                    }
                }
            }
            // The harness script reads outputs one tick later than the simulator records them
            // (calibrated: every program shows exactly this shift), so game[i + 1] ~ sim[i].
            const OFFSET: usize = 1;
            if actual.len() != expected.len() {
                eprintln!("game trace has {} ticks, simulator {}", actual.len(), expected.len());
                return Err(ExitCode::FAILURE);
            }
            let n = expected.len() - OFFSET;
            let mismatches: Vec<usize> = (0..n).filter(|&i| expected[i] != actual[i + OFFSET]).collect();
            if mismatches.is_empty() {
                let changes = (1..n).filter(|&i| expected[i] != expected[i - 1]).count();
                eprintln!("MATCH: {n} ticks identical in game and simulator ({changes} output changes)");
                Ok(())
            } else {
                eprintln!("MISMATCH at {} tick(s); first few:", mismatches.len());
                for &i in mismatches.iter().take(10) {
                    eprintln!("  tick {i}: simulator {:?}, game {:?}", expected[i], actual[i + OFFSET]);
                }
                Err(ExitCode::FAILURE)
            }
        }),
        Cmd::Decode { input } => {
            let text = std::fs::read_to_string(&input).unwrap_or(input);
            match blueprint::decode(&text) {
                Ok(v) => {
                    println!("{}", serde_json::to_string_pretty(&v).unwrap());
                    Ok(())
                }
                Err(e) => {
                    eprintln!("error: {e}");
                    Err(ExitCode::FAILURE)
                }
            }
        }
    };
    match res {
        Ok(()) => ExitCode::SUCCESS,
        Err(c) => c,
    }
}

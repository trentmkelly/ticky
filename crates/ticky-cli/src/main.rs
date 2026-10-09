use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::{Parser, Subcommand};
use ticky_compiler::program::Ty;
use ticky_compiler::testrun::{run_tests, Harness, PVal};
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
        /// Don't warn about signal names Ticky doesn't know (modded names).
        #[arg(long)]
        allow_unknown_signals: bool,
        /// Compile with runtime checks (see `build --checks`).
        #[arg(long)]
        checks: bool,
    },
    /// Simulate and print output ports whenever they change.
    Sim {
        file: PathBuf,
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
    /// Output ports on the `east` (default) or `west` edge. With `west` the output ports sit
    /// north of the blueprint at the west edge (the first output northernmost), each fed by
    /// its own line of poles from a gate on the east edge.
    #[arg(long, default_value = "east", value_parser = parse_side)]
    outputs: Side,
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
}

fn parse_side(s: &str) -> Result<Side, String> {
    match s {
        "east" => Ok(Side::East),
        "west" => Ok(Side::West),
        _ => Err("expected `east` or `west`".into()),
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

fn print_diags(diags: &[Diag], file: &str, src: &str) {
    for d in diags {
        eprint!("{}", d.render(file, src));
    }
}

fn build(file: &Path, autostart: bool, opt: Opt, place: &Placement) -> Result<(String, String, Compiled), ExitCode> {
    let (name, src) = load(file)?;
    let label = file.file_stem().map(|s| s.to_string_lossy().to_string()).unwrap_or_default();
    let opts = Options { autostart, label, opt, poles: !place.no_poles, outputs_west: place.outputs == Side::West, anneal: place.anneal(), allow_unknown_signals: place.allow_unknown_signals, quality: !place.no_quality, checks: place.checks };
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
        ports.push(format!(
            "{{name={}, dir={}, entity={}, signal={}, bundle={}}}",
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
    format!(
        "return {{\n  bp = {},\n  ticks = {ticks},\n  run = {},\n  ports = {{{}}},\n  sets = {{{}}},\n}}\n",
        lua_str(&c.blueprint_string()),
        c.cg.run_switch + 1,
        ports.join(", "),
        sets.join(", ")
    )
}

fn default_place() -> Placement {
    Placement { no_poles: false, outputs: Side::East, place: "grid".into(), max_width: None, max_height: None, seed: 1, effort: 1.0, allow_unknown_signals: false, no_quality: false, checks: false }
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
        Cmd::Test { file, allow_unknown_signals, checks } => build(&file, false, Opt::Speed, &Placement { allow_unknown_signals, checks, ..default_place() }).and_then(|(name, src, c)| {
            let results = run_tests(&c, &src);
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
        Cmd::Sim { file, ticks, sets, all, allow_unknown_signals, checks } => build(&file, false, Opt::Speed, &Placement { allow_unknown_signals, checks, ..default_place() }).and_then(|(_, _, c)| {
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
            let status = cmd.arg(&job).status();
            if !matches!(status, Ok(s) if s.success()) {
                eprintln!("error: harness failed ({})", script.display());
                return Err(ExitCode::FAILURE);
            }
            let trace = std::fs::read_to_string("/tmp/ticky-harness/script-output/ticky/trace.txt").map_err(|e| {
                eprintln!("error: no trace from the game: {e}");
                ExitCode::FAILURE
            })?;
            let expected: Vec<Vec<String>> = expected.iter().map(|r| r.iter().map(canonical).collect()).collect();
            let actual: Vec<Vec<String>> =
                trace.lines().map(|l| l.split_whitespace().skip(1).map(|v| v.to_string()).collect()).collect();
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

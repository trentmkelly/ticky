//! Profile-guided optimisation (`ticky test --profile`, `ticky build --profile`): profiles
//! record what the tests ran, a profiled build passes the same tests, and without a profile
//! (or with one that changes nothing) the circuit is exactly the plain one.

use std::path::Path;

use ticky_compiler::profile::Profile;
use ticky_compiler::testrun::{raw_steps, run_tests, run_tests_profiled};
use ticky_compiler::{compile, Compiled, Options};

fn build(src: &str, checks: bool, profile: Option<&Profile>) -> Compiled {
    let opts = Options { label: "test".into(), checks, profile: profile.cloned(), ..Default::default() };
    compile(src, &opts).unwrap_or_else(|d| panic!("{}", d.iter().map(|d| d.render("test", src)).collect::<String>()))
}

/// Total ticks of the program's tests, which must all pass.
fn passes(c: &Compiled, src: &str, what: &str) -> u64 {
    run_tests(c, src)
        .into_iter()
        .map(|r| {
            if let Some(d) = r.failure {
                panic!("{what}: test {} failed:\n{}", r.name, d.render(what, src));
            }
            r.ticks
        })
        .sum()
}

fn profile_of(src: &str, checks: bool) -> Profile {
    let c = build(src, checks, None);
    let (results, p) = run_tests_profiled(&c, src);
    assert!(results.iter().all(|r| r.failure.is_none()));
    p
}

const PRIMES: &str = include_str!("../../../examples/primes.ticky");

#[test]
fn profile_counts_steps_and_branches() {
    let c = build(PRIMES, false, None);
    let (_, p) = run_tests_profiled(&c, PRIMES);
    let main = &p.procs["main"];
    // The inner loop's test `k % d == 0` runs once per trial division: 236 for the numbers
    // below 100, 74 of them finding a divisor. (Its step is the `while` on line 10: the
    // loop's first statement.)
    let json = p.to_json(&raw_steps(&c), PRIMES);
    let steps = json["processes"][0]["steps"].as_array().unwrap();
    let branch = steps
        .iter()
        .find(|s| s["line"] == 10 && s["branch"]["taken"] == 74)
        .unwrap_or_else(|| panic!("no such branch on line 10 in {json}"));
    assert_eq!(branch["visits"], 236);
    assert_eq!(branch["branch"]["taken"], 74);
    assert_eq!(branch["branch"]["not_taken"], 162);
    // Every visit leaves the step somewhere (the program halts at the end).
    for (i, (_, visits)) in main.steps.iter().enumerate() {
        let out: u64 = main.edges.iter().filter(|((from, _), _)| *from == i).map(|(_, n)| n).sum();
        assert_eq!(out, *visits, "step {i}");
    }
    assert_eq!(main.edges.iter().filter(|((_, to), _)| to.is_none()).map(|(_, n)| n).sum::<u64>(), 1);
    // The file reads back as the same profile.
    assert_eq!(Profile::from_json(&json).unwrap(), p);
}

#[test]
fn hot_loop_gets_fewer_ticks_per_iteration() {
    // PGO's own decisions, without overlapping loop iterations (modsched; see below).
    ticky_compiler::modsched::set_disabled(true);
    let profile = profile_of(PRIMES, false);
    let plain = build(PRIMES, false, None);
    let guided = build(PRIMES, false, Some(&profile));
    ticky_compiler::modsched::set_disabled(false);
    // Without the profile the trial-division loop is two steps (2 + 3 ticks); with it, the
    // hot side (no divisor: `d += 1`) is merged into the test, run speculatively (`d` is
    // dead when a divisor is found): one 3-tick step.
    let loop_ticks = |c: &Compiled| -> Vec<String> {
        c.cg.procs[0].steps.iter().filter(|s| s.self_loop).map(|s| s.duration.clone()).collect()
    };
    assert_eq!(loop_ticks(&plain), Vec::<String>::new());
    assert_eq!(loop_ticks(&guided), vec!["3 ticks".to_string()]);
    let (before, after) = (passes(&plain, PRIMES, "plain"), passes(&guided, PRIMES, "guided"));
    assert!(after * 100 <= before * 85, "{before} → {after} ticks");
    let count = |c: &Compiled| c.cg.netlist.entities.iter().filter(|e| e.kind.is_combinator()).count();
    assert!(count(&guided) <= count(&plain), "{} → {} combinators", count(&plain), count(&guided));
    let (est_plain, est_guided) = guided.profiled.unwrap();
    assert!(est_guided < est_plain);
    assert!(plain.profiled.is_none());
}

/// With overlapping loop iterations on top, the merged loop pipelines further: one 2-tick step
/// (spending combinators for ticks, as `--opt=speed` may).
#[test]
fn hot_loop_with_overlapped_iterations() {
    let profile = profile_of(PRIMES, false);
    let plain = build(PRIMES, false, None);
    let guided = build(PRIMES, false, Some(&profile));
    let loop_ticks = |c: &Compiled| -> Vec<String> {
        c.cg.procs[0].steps.iter().filter(|s| s.self_loop).map(|s| s.duration.clone()).collect()
    };
    assert_eq!(loop_ticks(&guided), vec!["2 ticks".to_string()]);
    let (before, after) = (passes(&plain, PRIMES, "plain"), passes(&guided, PRIMES, "guided"));
    assert!(after * 100 <= before * 70, "{before} → {after} ticks");
}

/// Every example: its profiled build passes its tests, and when the profile doesn't pay
/// off the build is exactly the plain one (as it is with a profile where nothing ran).
#[test]
fn profiled_examples_pass_their_tests() {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut guided = 0;
    for entry in std::fs::read_dir(&dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_none_or(|e| e != "ticky") {
            continue;
        }
        let src = std::fs::read_to_string(&path).unwrap();
        let name = path.display().to_string();
        let checks = src.starts_with("# ticky: --checks");
        let profile = profile_of(&src, checks);
        let plain = build(&src, checks, None);
        let c = build(&src, checks, Some(&profile));
        passes(&c, &src, &name);
        let (before, after) = c.profiled.unwrap();
        if after < before {
            guided += 1;
        } else {
            assert_eq!(c.blueprint_json(), plain.blueprint_json(), "{name}");
        }
        // A profile where nothing ran changes nothing.
        let mut idle = profile.clone();
        for p in idle.procs.values_mut() {
            p.edges.clear();
            p.steps.iter_mut().for_each(|s| s.1 = 0);
        }
        assert_eq!(build(&src, checks, Some(&idle)).blueprint_json(), plain.blueprint_json(), "{name} (idle profile)");
    }
    // primes, sorting, production-moments, functions, thruster (as of writing).
    assert!(guided >= 3, "only {guided} examples changed by their profiles");
}

#[test]
fn stale_or_mismatched_profiles_are_ignored() {
    let profile = profile_of(PRIMES, false);
    let plain = build(PRIMES, false, None);
    // Edited source: the profile is ignored, with a warning.
    let edited = PRIMES.replace("max 5000 ticks", "max 6000 ticks");
    let c = build(&edited, false, Some(&profile));
    assert!(c.warnings.iter().any(|w| w.message.contains("different version")));
    assert_eq!(c.blueprint_json(), build(&edited, false, None).blueprint_json());
    // Same source hash but steps that don't match: that process's profile is ignored.
    let mut wrong = profile.clone();
    wrong.procs.get_mut("main").unwrap().steps.pop();
    let c = build(PRIMES, false, Some(&wrong));
    assert!(c.warnings.iter().any(|w| w.message.contains("don't match")), "{:?}", c.warnings.iter().map(|w| &w.message).collect::<Vec<_>>());
    assert_eq!(c.blueprint_json(), plain.blueprint_json());
    // `--opt=size` doesn't use profiles.
    let size = Options { opt: ticky_compiler::Opt::Size, profile: Some(profile), ..Default::default() };
    let c = compile(PRIMES, &size).unwrap();
    assert!(c.warnings.iter().any(|w| w.message.contains("only guides --opt=speed")));
    assert_eq!(c.blueprint_json(), compile(PRIMES, &Options { opt: ticky_compiler::Opt::Size, ..Default::default() }).unwrap().blueprint_json());
}

/// Speculation leaves alone what others can see: here the hot side also writes an output
/// (and a variable another process reads), which must keep their values when the loop
/// leaves by the cold side. (The merge itself is checked in `cfg::tests`; here it doesn't
/// pay off, and the plain build is kept.)
#[test]
fn speculation_spares_visible_writes() {
    let src = r#"
input  n: int @ N
output probe: int @ P
output first: int @ F
output done: bool @ D
seen = 0
done = False
d = 2
probe = 0
while d < n:
    if n % d == 0:
        first = d
        break
    d += 1
    probe = d
    seen = d
done = True

process watch:
    while True:
        wait until seen > 0
        wait until done

test "smallest factor":
    set n = 899
    run until done, max 2000 ticks
    assert first == 29 and probe == 29
"#;
    let profile = profile_of(src, false);
    let c = build(src, false, Some(&profile));
    passes(&c, src, "guided");
    // Without the visible writes, `d` alone is speculated and the loop gets faster.
    let quiet = src.replace("    probe = d\n    seen = d\n", "").replace("first == 29 and probe == 29", "first == 29");
    let c = build(&quiet, false, Some(&profile_of(&quiet, false)));
    assert!(c.profiled.is_some_and(|(b, a)| a < b), "{:?}", c.profiled);
    passes(&c, &quiet, "guided, quiet");
}

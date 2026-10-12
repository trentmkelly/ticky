use ticky_compiler::{compile, Compiled, Options};
use ticky_compiler::program::{Next, StepKind};
use ticky_compiler::testrun::{Harness, PVal};

fn build(src: &str, checks: bool) -> Compiled {
    compile(src, &Options { checks, poles: false, ..Default::default() }).unwrap()
}
fn value(h: &Harness<'_>, name: &str) -> i32 {
    let PVal::Int(v) = h.get(h.c.program.port_index(name).unwrap()) else { panic!() };
    v
}
fn set(h: &mut Harness<'_>, name: &str, v: i32) {
    h.set(h.c.program.port_index(name).unwrap(), PVal::Int(v));
}
fn count(c: &Compiled) -> usize {
    c.cg.netlist.entities.iter().filter(|e| e.kind.is_combinator()).count()
}

#[test]
fn identical_branch_targets_discard_dead_predicate_but_keep_checks() {
    let src = "input ready: bool\ninput x: int\noutput y: int\nwhile True:\n    wait until ready\n    if (x * 73) % 101 > 50:\n        continue\n    else:\n        continue\n";
    let c = build(src, false);
    assert!(!c.program.procs[0].steps.iter().any(|s| matches!(s.kind, StepKind::Run(Next::Branch(..)))));
    let simple = build("input ready: bool\ninput x: int\noutput y: int\nwhile True:\n    wait until ready\n", false);
    // The unused predicate's input may still have a sample register, but no arithmetic cone.
    assert!(count(&c) <= count(&simple) + 2, "{} vs {}", count(&c), count(&simple));

    let checked = src.replace("(x * 73) % 101", "100 // x");
    let c = build(&checked, true);
    assert!(c.program.procs[0].steps.iter().any(|s| !s.checks.is_empty()));
    let mut h = Harness::new(&c);
    set(&mut h, "ready", 1);
    set(&mut h, "x", 0);
    for _ in 0..100 { h.sim.step(); }
    assert_ne!(value(&h, "error"), 0, "removed branch must still check division by zero");
}

#[test]
fn checks_in_otherwise_empty_step_are_not_threaded_away() {
    let c = build("input x: int\noutput y: int\nassert x != 0\nwait 5\ny = 1\n", true);
    let mut h = Harness::new(&c);
    for _ in 0..60 { h.sim.step(); }
    assert_ne!(value(&h, "error"), 0);
    assert_eq!(value(&h, "y"), 0);
}

#[test]
fn common_live_wait_tail_is_shared_without_changing_its_predecessors() {
    let src = "input choose: bool\ninput ready: bool\noutput result: int\nif choose:\n    wait 5\n    wait until ready\nelse:\n    wait 7\n    wait until ready\nresult = 1\n";
    let c = build(src, false);
    assert_eq!(c.program.procs[0].steps.iter().filter(|s| matches!(s.kind, StepKind::WaitUntil(..))).count(), 1);
    for choose in [0, 1] {
        let mut h = Harness::new(&c);
        set(&mut h, "choose", choose);
        for _ in 0..30 { h.sim.step(); }
        assert_eq!(value(&h, "result"), 0);
        set(&mut h, "ready", 1);
        for _ in 0..15 { h.sim.step(); }
        assert_eq!(value(&h, "result"), 1);
    }
}

#[test]
fn shared_wait_commits_preserve_exact_tick_count_and_restart() {
    let c = build("output result: int\nwait 10\nwait 10\nwait 10\nwait 10\nresult = 1\n", false);
    let reference = build("output result: int\nwait 40\nresult = 1\n", false);
    assert_eq!(c.program.procs[0].steps.len(), 5, "wait boundaries are retained");
    let commits = c.cg.netlist.entities.iter().filter(|e| e.description.as_deref().is_some_and(|d| d.contains(": shared action-free commit"))).count();
    assert_eq!(commits, 1, "all four waits advance the PC by one");
    assert_eq!(count(&c), count(&reference), "four wait states need only one commit decider");
    let mut a = Harness::new(&c);
    let mut b = Harness::new(&reference);
    for tick in 0..160 {
        if tick == 70 || tick == 90 {
            a.sim.set_constant_on(c.cg.run_switch, tick == 90);
            b.sim.set_constant_on(reference.cg.run_switch, tick == 90);
        }
        a.sim.step(); b.sim.step();
        assert_eq!(value(&a, "result"), value(&b, "result"), "tick {tick}");
    }
}

#[test]
fn cleanup_of_an_empty_cycle_terminates() {
    let c = build("input x: int\noutput y: int\nwhile True:\n    if x:\n        continue\n    else:\n        continue\n", false);
    assert_eq!(c.program.procs[0].steps.len(), 1);
    let mut h = Harness::new(&c);
    for tick in 0..100 { set(&mut h, "x", tick % 2); h.sim.step(); }
    assert_eq!(value(&h, "y"), 0);
}

#[test]
fn consecutive_dynamic_waits_resample_their_duration() {
    let c = build("input n: int\noutput result: int\nwait n\nwait n\nresult = 1\n", false);
    let mut h = Harness::new(&c);
    set(&mut h, "n", 10);
    for _ in 0..8 { h.sim.step(); }
    // The first wait has already sampled ten; the next must sample twenty.
    set(&mut h, "n", 20);
    for _ in 0..18 { h.sim.step(); }
    assert_eq!(value(&h, "result"), 0, "second wait reused the first sampled duration");
    for _ in 0..20 { h.sim.step(); }
    assert_eq!(value(&h, "result"), 1);
}

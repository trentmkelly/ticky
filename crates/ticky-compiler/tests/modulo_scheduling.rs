//! Overlapping loop iterations (`crate::modsched`, PLAN.md §7): a loop step computes the
//! next iteration's induction-variable work while it runs, so it gets shorter; everything
//! a program can observe (output values and the order they change in, final values, checks)
//! is the same as without the pass.

use ticky_compiler::testrun::{run_tests, Harness, PVal};
use ticky_compiler::{compile, modsched, Compiled, Opt, Options};

fn build(src: &str, opt: Opt, checks: bool, pipelined: bool) -> Compiled {
    modsched::set_disabled(!pipelined);
    let c = compile(src, &Options { label: "t".into(), opt, checks, ..Default::default() });
    modsched::set_disabled(false);
    c.unwrap_or_else(|d| panic!("{}", d.iter().map(|d| d.render("t", src)).collect::<String>()))
}

fn count(c: &Compiled) -> usize {
    c.cg.netlist.entities.iter().filter(|e| e.kind.is_combinator()).count()
}

/// Ticks per iteration of every loop step (a step that branches to itself).
fn loop_ticks(c: &Compiled) -> Vec<u32> {
    c.program
        .procs
        .iter()
        .flat_map(|m| m.steps.iter().enumerate().filter(|(i, s)| s.targets().contains(&Some(*i))).map(|(_, s)| s.depth.max(1) + 1))
        .collect()
}

/// Loops transformed: registers of the pass among the states.
fn pipelined(c: &Compiled) -> usize {
    c.program.states.iter().filter(|s| std::iter::once(&s.name).chain(&s.shared).any(|n| n.contains("#m"))).count()
}

/// Runs `c` with `inputs` for `ticks` ticks: every output's sequence of values (each change
/// once, in order), and the tick `done` (if there is one) first became 1.
fn run(c: &Compiled, inputs: &[(&str, i32)], ticks: u32) -> (Vec<(String, Vec<i32>)>, Option<u32>) {
    let mut h = Harness::new(c);
    for (n, v) in inputs {
        h.set(c.program.port_index(n).unwrap(), PVal::Int(*v));
    }
    let outs: Vec<(usize, String)> = c
        .program
        .ports
        .iter()
        .enumerate()
        .filter(|(_, p)| p.dir == ticky_syntax::ast::PortDir::Output)
        .map(|(i, p)| (i, p.name.clone()))
        .collect();
    let mut seqs: Vec<(String, Vec<i32>)> = outs.iter().map(|(_, n)| (n.clone(), vec![0])).collect();
    let mut done = None;
    for t in 0..ticks {
        h.sim.step();
        for (k, (pi, n)) in outs.iter().enumerate() {
            let PVal::Int(v) = h.get(*pi) else { continue };
            if seqs[k].1.last() != Some(&v) {
                seqs[k].1.push(v);
            }
            if n == "done" && v == 1 && done.is_none() {
                done = Some(t);
            }
        }
    }
    (seqs, done)
}

const POLY: &str = "input n: int @ N
output total: int @ T
output done: bool @ D

while True:
    wait until n != 0
    done = False
    s = 0
    k = n
    for i in range(20):
        s += (i * i * 3 + i * k) % 11
    total = s
    done = True
    wait until n == 0

test \"sum\":
    set n = 5
    run until done, max 400 ticks
    assert total == 77
";

#[test]
fn independent_work_overlaps_the_next_iteration() {
    let plain = build(POLY, Opt::Speed, false, false);
    let fast = build(POLY, Opt::Speed, false, true);
    assert_eq!(loop_ticks(&plain), vec![8]);
    // `(i*i*3 + i*k) % 11` for the next `i` is computed while this iteration adds: two
    // rounds, so the loop step is only as deep as the floor modulo and the sum.
    assert!(loop_ticks(&fast).iter().all(|&t| t <= 4), "{:?}", loop_ticks(&fast));
    assert!(pipelined(&fast) > 0);
    for c in [&plain, &fast] {
        assert!(run_tests(c, POLY).iter().all(|r| r.failure.is_none()));
    }
    for n in [5, -7, 1, 46341, i32::MAX, i32::MIN + 1, -1] {
        let (a, ta) = run(&plain, &[("n", n)], 400);
        let (b, tb) = run(&fast, &[("n", n)], 400);
        assert_eq!(a, b, "n = {n}");
        assert!(tb.unwrap() + 60 <= ta.unwrap(), "n = {n}: {tb:?} vs {ta:?}");
    }
    // Not under `--opt=size` (no ticks are bought there).
    let size = build(POLY, Opt::Size, false, true);
    assert_eq!(pipelined(&size), 0);
    assert_eq!(count(&size), count(&build(POLY, Opt::Size, false, false)));
}

/// Loops that run zero times or once, count down, start with their increment, nest, write
/// outputs every iteration, or live in a process behind a handshake.
const SHAPES: &str = "input n: int @ N
input m: int @ M
output a: int @ A
output b: int @ B
output c: int @ C
output trace: int @ E
output r1: int @ F
output done: bool @ D

r = 0
ready = False

process helper:
    wait until n != 0
    q = n * 3
    t = 0
    for j in range(7):
        t += (j * q + 5) * (j - q)
    r = t
    ready = True

wait until n != 0
z = m
x = 0
for i in range(z):
    x += (i * i + z) * 3 - i
a = x
y = 0
w = 0
while w < 9:
    w += 1
    y += (w * w * 5 + z) % 7 + w * 2
b = y
p = 0
for i in range(30, 0, -4):
    for j in range(3):
        p += (i * j + z) * (j + 1)
    trace = (i * 7 + z) % 13
c = p
wait until ready
r1 = r
done = True
";

#[test]
fn edge_cases_match_the_plain_build() {
    let checks = [false, true];
    for ch in checks {
        let plain = build(SHAPES, Opt::Speed, ch, false);
        let fast = build(SHAPES, Opt::Speed, ch, true);
        assert!(pipelined(&fast) > 0, "something to pipeline (checks {ch})");
        for (n, m) in [(1, 0), (4, 1), (-3, 2), (7, 5), (100000, -4), (i32::MAX, 3)] {
            let (x, tx) = run(&plain, &[("n", n), ("m", m)], 3000);
            let (y, ty) = run(&fast, &[("n", n), ("m", m)], 3000);
            assert_eq!(x, y, "n = {n}, m = {m}, checks {ch}");
            assert!(tx.is_some() && ty.is_some());
        }
    }
}

/// `100 // (4 - i)` for the iteration after the last one divides by zero: under `--checks`
/// a value that can fail is never computed early, so no error is raised.
const DIVIDE: &str = "input go: bool @ G
output s: int @ S
output done: bool @ D
while True:
    wait until go
    t = 0
    for i in range(4):
        t += 100 // (4 - i) + i * i * 7
    s = t
    done = True
    wait until not go
";

#[test]
fn speculative_values_never_fail_checks() {
    for ch in [false, true] {
        let fast = build(DIVIDE, Opt::Speed, ch, true);
        let (out, done) = run(&fast, &[("go", 1)], 300);
        assert!(done.is_some());
        let get = |n: &str| out.iter().find(|(m, _)| m == n).map(|(_, v)| *v.last().unwrap());
        assert_eq!(get("s"), Some(25 + 33 + 50 + 100 + 7 * (1 + 4 + 9)));
        if ch {
            assert_eq!(get("error"), Some(0), "no error from a value computed past the exit");
        }
    }
}

/// No example loop gets slower, and every example still passes its tests. (When this was
/// written, none changed at all: production-moments' loop is long only because of dead
/// arithmetic, whose timing `prune_dead_stores` deliberately keeps, and the other loops'
/// steps are as long as their recurrences or read inputs.)
#[test]
fn examples_never_get_slower() {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/../../examples");
    let mut files: Vec<_> = std::fs::read_dir(dir).unwrap().map(|e| e.unwrap().path()).filter(|p| p.extension().is_some_and(|e| e == "ticky")).collect();
    files.sort();
    for f in files {
        let src = std::fs::read_to_string(&f).unwrap();
        // `# ticky: --checks` on the first line: the tests need runtime checks.
        let checks = src.starts_with("# ticky: --checks");
        let a = build(&src, Opt::Speed, checks, false);
        let b = build(&src, Opt::Speed, checks, true);
        let (ta, tb) = (loop_ticks(&a), loop_ticks(&b));
        assert_eq!(ta.len(), tb.len(), "{}", f.display());
        assert!(ta.iter().zip(&tb).all(|(x, y)| y <= x), "{}: {ta:?} → {tb:?}", f.display());
        for r in run_tests(&b, &src) {
            assert!(r.failure.is_none(), "{}: test {} failed", f.display(), r.name);
        }
    }
    let src = include_str!("../../../examples/production-moments.ticky");
    assert_eq!(pipelined(&build(src, Opt::Speed, false, true)), 0, "dead arithmetic sets that loop's step");
}

use ticky_compiler::{compile, testrun::run_tests, Options};

fn check(src: &str, max_combinators: usize) {
    let c = compile(src, &Options::default()).unwrap_or_else(|d| panic!("{}", d[0].message));
    assert!(c.cg.netlist.validate(true).is_empty());
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "{}: {:?}", r.name, r.failure);
    }
    let n = c.cg.netlist.entities.iter().filter(|e| e.kind.is_combinator()).count();
    eprintln!("{n} combinators");
    assert!(n <= max_combinators, "{n} combinators, expected at most {max_combinators}");
}

#[test]
fn large_scalar_extrema_preserve_i32_and_zero() {
    let args = (0..32).map(|i| format!("a ^ {i}")).collect::<Vec<_>>().join(", ");
    let src = format!(r#"input a: int @ A
output lo: int @ L
output hi: int @ H
every tick:
    lo = min({args})
    hi = max({args})
test "extrema":
    set a = 0
    run 120 ticks
    assert lo == 0 and hi == 31
    set a = -1
    run 120 ticks
    assert lo == -32 and hi == -1
    set a = -2147483648
    run 120 ticks
    assert lo == -2147483648 and hi == -2147483617
    set a = 2147483647
    run 120 ticks
    assert lo == 2147483616 and hi == 2147483647
"#);
    // 74 combinators before whole-tree extrema recognition.
    check(&src, 47);
}

#[test]
fn argmax_shares_score_with_labels_and_preserves_ties() {
    for period in ["tick", "120 ticks"] {
        let src = format!(r#"input a: int @ A
input b: int @ B
input c: int @ C
input d: int @ D
output score: int @ S
output winner: int @ W
output floor_score: int @ F
output floor_winner: int @ G
output middle: int @ M

def choose(floor):
    best, top = -2147483648, floor
    if a > top:
        best, top = 2147483647, a
    if b > top:
        best, top = 7, b
    mid = top
    if c > top:
        best, top = -2, c
    if d > top:
        best, top = 0, d
    return best, top, mid

every {period}:
    winner, score, middle = choose(0)
    floor_winner, floor_score, unused = choose(5)

test "winner and score":
    set a = -2147483648
    set b = -1
    set c = 0
    set d = 0
    run 300 ticks
    assert score == 0 and winner == -2147483648 and middle == 0
    assert floor_score == 5 and floor_winner == -2147483648
    set a = 5
    set b = 5
    set c = 5
    set d = 5
    run 300 ticks
    assert score == 5 and winner == 2147483647 and middle == 5
    assert floor_score == 5 and floor_winner == -2147483648
    set a = 2147483647
    set b = 2147483647
    set c = 10
    set d = 8
    run 300 ticks
    assert score == 2147483647 and winner == 2147483647
    assert floor_score == 2147483647 and floor_winner == 2147483647
    set a = 1
    set b = 2
    set c = 3
    set d = 9
    run 300 ticks
    assert score == 9 and winner == 0 and middle == 2
    assert floor_score == 9 and floor_winner == 0
"#);
        // Previously 98 pipelined / 75 periodic, including the externally used midpoint.
        check(&src, if period == "tick" { 51 } else { 41 });
    }
}

#[test]
fn profitable_sort_group_survives_unrelated_candidates() {
    let src = r#"input a: int @ A
input b: int @ B
input c: int @ C
input d: int @ D
output first: int @ F
output second: int @ S
output noise: int @ N

def sort(xs):
    for i in range(len(xs) - 1):
        for j in range(len(xs) - 1 - i):
            if xs[j] > xs[j + 1]:
                t = xs[j]
                xs[j] = xs[j + 1]
                xs[j + 1] = t
    return xs

every 120 ticks:
    xs = sort([a, b, c, d])
    first = xs[1]
    second = xs[2]
NOISE

test "grouped ranks":
    set a = 0
    set b = 0
    set c = 0
    set d = 0
    run 300 ticks
    assert first == 0 and second == 0 and noise == EXPECT_ZERO
    set a = -2147483648
    set b = 2147483647
    set c = 0
    set d = -1
    run 300 ticks
    assert first == -1 and second == 0 and noise == EXPECT_EXTREME
"#;
    let terms: Vec<_> = (1..=12).map(|i| {
        let (x, y, z) = (i * 42, i * 37, i * 21);
        format!("min(a ^ {x}, b ^ {y}, c ^ {z}) + min(b ^ {y}, c ^ {z})")
    }).collect();
    let noise = format!("    noise = {}", terms.join(" + "));
    let expected = |a: i32, b: i32, c: i32| (1..=12).fold(0i32, |acc, i| {
        let (x, y, z) = (a ^ (i * 42), b ^ (i * 37), c ^ (i * 21));
        acc.wrapping_add(x.min(y).min(z)).wrapping_add(y.min(z))
    });
    let src = src.replace("NOISE", &noise)
        .replace("EXPECT_ZERO", &expected(0, 0, 0).to_string())
        .replace("EXPECT_EXTREME", &expected(i32::MIN, i32::MAX, 0).to_string());
    // Previously 196: all candidates together lost to unrelated shared min subtrees.
    check(&src, 174);
}

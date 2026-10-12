//! Bounded Boolean cover reduction. Terms are sets, independent of literal order.
//! Only exact complements are used: integer comparisons retain their signed semantics.

pub(crate) fn simplify_terms<T: Copy + Eq>(terms: Vec<Vec<T>>, negate: impl Fn(T) -> T) -> Vec<Vec<T>> {
    // Callers have separate emission limits. Avoid expensive quadratic work on an
    // unexpectedly large intermediate cover, without changing its meaning.
    if terms.len() > 256 || terms.iter().map(Vec::len).sum::<usize>() > 8192 {
        return terms;
    }
    let mut out: Vec<Vec<T>> = Vec::new();
    for term in terms {
        let mut unique = Vec::new();
        for l in term {
            if !unique.contains(&l) {
                unique.push(l);
            }
        }
        if !unique.iter().any(|&l| unique.contains(&negate(l))) {
            out.push(unique);
        }
    }
    loop {
        // Absorption also canonicalizes equal terms in different literal orders.
        let mut i = 0;
        while i < out.len() {
            if (0..out.len()).any(|j| i != j && out[j].iter().all(|l| out[i].contains(l))) {
                out.remove(i);
            } else {
                i += 1;
            }
        }
        // (P and q) or (P and not q) = P. Replace two terms by one,
        // so every iteration strictly shrinks the cover.
        let pair = (0..out.len()).find_map(|i| {
            (i + 1..out.len()).find_map(|j| {
                let a: Vec<_> = out[i].iter().filter(|l| !out[j].contains(l)).copied().collect();
                let b: Vec<_> = out[j].iter().filter(|l| !out[i].contains(l)).copied().collect();
                (a.len() == 1 && b.len() == 1 && negate(a[0]) == b[0]).then_some((i, j, a))
            })
        });
        let Some((i, j, a)) = pair else { return out };
        out[i].retain(|l| *l != a[0]);
        out.remove(j);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn covers_preserve_all_small_truth_tables() {
        let terms = vec![vec![], vec![1], vec![-1], vec![2], vec![-2], vec![1, 2], vec![1, -2], vec![-1, 2], vec![-1, -2], vec![2, 1], vec![1, -1]];
        for mask in 0..1usize << terms.len() {
            let d: Vec<_> = terms.iter().enumerate().filter(|(i, _)| mask & (1 << i) != 0).map(|(_, t)| t.clone()).collect();
            let reduced = simplify_terms(d.clone(), |x: i32| -x);
            for bits in 0..4 {
                let eval = |d: &Vec<Vec<i32>>| d.iter().any(|t| t.iter().all(|&l| ((bits & (1 << (l.abs() - 1))) != 0) == (l > 0)));
                assert_eq!(eval(&d), eval(&reduced), "{d:?} -> {reduced:?}");
            }
        }
        assert_eq!(simplify_terms(vec![vec![1, 2], vec![-2, 1]], |x| -x), vec![vec![1]]);
        assert_eq!(simplify_terms(vec![vec![1], vec![1, 2]], |x| -x), vec![vec![1]]);
    }
}

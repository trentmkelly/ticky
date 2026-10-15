//! Harvested patterns: the s-expressions `fuse::superopt::harvest` writes, their exact
//! semantics (the IR's: Factorio's `ArOp::apply`, comparisons 0/1, selects as sums of
//! guarded arms), and the alphabet a search over them draws from.

use ticky_factorio::{ArOp, CmpOp};

#[derive(Clone, Debug, PartialEq)]
pub enum Pat {
    X(usize),
    K(i32),
    /// The condition of a select arm worth 0 (not read).
    Hole,
    Ar(ArOp, Box<Pat>, Box<Pat>),
    Cmp(CmpOp, Box<Pat>, Box<Pat>),
    /// `(t ? a : 0) + (f ? b : 0)`.
    Mux(Box<Pat>, Box<Pat>, Box<Pat>, Box<Pat>),
    /// Σ k over the arms whose DNF holds.
    Dec(Vec<(i32, Vec<Vec<(CmpOp, Pat, Pat)>>)>),
    /// Σ c ? x : 0.
    Sel(Vec<(Pat, Pat)>),
}

pub fn ar_op(s: &str) -> Option<ArOp> {
    Some(match s {
        "mul" => ArOp::Mul,
        "div" => ArOp::Div,
        "add" => ArOp::Add,
        "sub" => ArOp::Sub,
        "mod" => ArOp::Mod,
        "pow" => ArOp::Pow,
        "shl" => ArOp::Shl,
        "shr" => ArOp::Shr,
        "and" => ArOp::And,
        "or" => ArOp::Or,
        "xor" => ArOp::Xor,
        _ => return None,
    })
}

pub fn cmp_op(s: &str) -> Option<CmpOp> {
    Some(match s {
        "lt" => CmpOp::Lt,
        "gt" => CmpOp::Gt,
        "eq" => CmpOp::Eq,
        "ge" => CmpOp::Ge,
        "le" => CmpOp::Le,
        "ne" => CmpOp::Ne,
        _ => return None,
    })
}

pub const ALL_AR: [ArOp; 11] = [ArOp::Mul, ArOp::Div, ArOp::Add, ArOp::Sub, ArOp::Mod, ArOp::Pow, ArOp::Shl, ArOp::Shr, ArOp::And, ArOp::Or, ArOp::Xor];
pub const ALL_CMP: [CmpOp; 6] = [CmpOp::Lt, CmpOp::Gt, CmpOp::Eq, CmpOp::Ge, CmpOp::Le, CmpOp::Ne];

/// Names as validate.py spells them.
pub fn ar_py(op: ArOp) -> &'static str {
    match op {
        ArOp::Mul => "Mul",
        ArOp::Div => "Div",
        ArOp::Add => "Add",
        ArOp::Sub => "Sub",
        ArOp::Mod => "Mod",
        ArOp::Pow => "Pow",
        ArOp::Shl => "Shl",
        ArOp::Shr => "Shr",
        ArOp::And => "And",
        ArOp::Or => "Or",
        ArOp::Xor => "Xor",
    }
}

pub fn cmp_py(op: CmpOp) -> &'static str {
    match op {
        CmpOp::Lt => "Lt",
        CmpOp::Gt => "Gt",
        CmpOp::Eq => "Eq",
        CmpOp::Ge => "Ge",
        CmpOp::Le => "Le",
        CmpOp::Ne => "Ne",
    }
}

#[derive(Debug)]
enum Sx {
    Atom(String),
    List(Vec<Sx>),
}

fn tokens(s: &str) -> Vec<String> {
    s.replace('(', " ( ").replace(')', " ) ").split_whitespace().map(String::from).collect()
}

fn sx(t: &[String], i: &mut usize) -> Result<Sx, String> {
    let tok = t.get(*i).ok_or("unexpected end")?;
    *i += 1;
    if tok == "(" {
        let mut v = Vec::new();
        while t.get(*i).map(|s| s.as_str()) != Some(")") {
            if *i >= t.len() {
                return Err("unclosed (".into());
            }
            v.push(sx(t, i)?);
        }
        *i += 1;
        Ok(Sx::List(v))
    } else if tok == ")" {
        Err("unexpected )".into())
    } else {
        Ok(Sx::Atom(tok.clone()))
    }
}

fn head(v: &[Sx]) -> Option<&str> {
    match v.first() {
        Some(Sx::Atom(a)) => Some(a),
        _ => None,
    }
}

fn to_pat(s: &Sx) -> Result<Pat, String> {
    match s {
        Sx::Atom(a) if a == "_" => Ok(Pat::Hole),
        Sx::Atom(a) if a.starts_with('x') => Ok(Pat::X(a[1..].parse().map_err(|_| format!("bad leaf {a}"))?)),
        Sx::Atom(a) => Ok(Pat::K(a.parse().map_err(|_| format!("bad constant {a}"))?)),
        Sx::List(v) => {
            let h = head(v).ok_or("empty list")?;
            let arg = |i: usize| -> Result<Box<Pat>, String> { Ok(Box::new(to_pat(v.get(i).ok_or("missing operand")?)?)) };
            if let Some(op) = ar_op(h) {
                return Ok(Pat::Ar(op, arg(1)?, arg(2)?));
            }
            if let Some(op) = cmp_op(h) {
                return Ok(Pat::Cmp(op, arg(1)?, arg(2)?));
            }
            match h {
                "mux" => Ok(Pat::Mux(arg(1)?, arg(2)?, arg(3)?, arg(4)?)),
                "sel" => {
                    let mut arms = Vec::new();
                    for p in v[1..].chunks(2) {
                        if p.len() != 2 {
                            return Err("odd sel".into());
                        }
                        arms.push((to_pat(&p[0])?, to_pat(&p[1])?));
                    }
                    Ok(Pat::Sel(arms))
                }
                "dec" => {
                    let mut arms = Vec::new();
                    for a in &v[1..] {
                        let Sx::List(a) = a else { return Err("bad arm".into()) };
                        let (Some("arm"), Some(Sx::Atom(k)), Some(Sx::List(or))) = (head(a), a.get(1), a.get(2)) else { return Err("bad arm".into()) };
                        let k: i32 = k.parse().map_err(|_| "bad arm constant")?;
                        let mut dnf = Vec::new();
                        for t in &or[1..] {
                            let Sx::List(t) = t else { return Err("bad term".into()) };
                            let mut lits = Vec::new();
                            for l in &t[1..] {
                                let Sx::List(l) = l else { return Err("bad literal".into()) };
                                let op = head(l).and_then(cmp_op).ok_or("bad comparison")?;
                                lits.push((op, to_pat(&l[1])?, to_pat(&l[2])?));
                            }
                            dnf.push(lits);
                        }
                        arms.push((k, dnf));
                    }
                    Ok(Pat::Dec(arms))
                }
                _ => Err(format!("unknown operator {h}")),
            }
        }
    }
}

impl Pat {
    pub fn parse(s: &str) -> Result<Pat, String> {
        let t = tokens(s);
        let mut i = 0;
        let p = to_pat(&sx(&t, &mut i)?)?;
        if i != t.len() {
            return Err("trailing tokens".into());
        }
        Ok(p)
    }

    pub fn eval(&self, x: &[i32]) -> i32 {
        let b = |c: bool| c as i32;
        match self {
            Pat::X(i) => x[*i],
            Pat::K(k) => *k,
            Pat::Hole => 0,
            Pat::Ar(op, a, c) => op.apply(a.eval(x), c.eval(x)),
            Pat::Cmp(op, a, c) => b(op.apply(a.eval(x), c.eval(x))),
            Pat::Mux(t, f, a, c) => {
                let ta = if **t != Pat::Hole && t.eval(x) != 0 { a.eval(x) } else { 0 };
                let fb = if **f != Pat::Hole && f.eval(x) != 0 { c.eval(x) } else { 0 };
                ta.wrapping_add(fb)
            }
            Pat::Dec(arms) => {
                let mut s = 0i32;
                for (k, d) in arms {
                    if d.iter().any(|t| t.iter().all(|(op, l, r)| op.apply(l.eval(x), r.eval(x)))) {
                        s = s.wrapping_add(*k);
                    }
                }
                s
            }
            Pat::Sel(arms) => arms.iter().filter(|(c, _)| c.eval(x) != 0).fold(0i32, |s, (_, v)| s.wrapping_add(v.eval(x))),
        }
    }

    fn walk<'a>(&'a self, f: &mut dyn FnMut(&'a Pat)) {
        f(self);
        match self {
            Pat::Ar(_, a, b) | Pat::Cmp(_, a, b) => {
                a.walk(f);
                b.walk(f);
            }
            Pat::Mux(t, g, a, b) => {
                for p in [t, g, a, b] {
                    p.walk(f);
                }
            }
            Pat::Dec(arms) => {
                for (_, d) in arms {
                    for (_, l, r) in d.iter().flatten() {
                        l.walk(f);
                        r.walk(f);
                    }
                }
            }
            Pat::Sel(arms) => {
                for (c, v) in arms {
                    c.walk(f);
                    v.walk(f);
                }
            }
            _ => {}
        }
    }

    /// Number of leaves (`x0`…): one more than the highest index.
    pub fn leaves(&self) -> usize {
        let mut n = 0;
        self.walk(&mut |p| {
            if let Pat::X(i) = p {
                n = n.max(i + 1);
            }
        });
        n
    }

    pub fn consts(&self) -> Vec<i32> {
        let mut out = Vec::new();
        self.walk(&mut |p| {
            if let Pat::K(k) = p {
                if !out.contains(k) {
                    out.push(*k);
                }
            }
        });
        if let Pat::Dec(arms) = self {
            for (k, _) in arms {
                if !out.contains(k) {
                    out.push(*k);
                }
            }
        }
        out
    }

    /// Comparisons of a leaf with a leaf or constant anywhere in the pattern, as
    /// `(op, leaf, Ok(leaf) | Err(constant))` with the leaf first, plus their negations.
    pub fn literals(&self) -> Vec<(CmpOp, usize, Result<usize, i32>)> {
        let mut out = Vec::new();
        let mut add = |op: CmpOp, a: &Pat, b: &Pat| {
            let lit = match (a, b) {
                (Pat::X(i), Pat::X(j)) => Some((op, *i, Ok(*j))),
                (Pat::X(i), Pat::K(k)) => Some((op, *i, Err(*k))),
                (Pat::K(k), Pat::X(i)) => Some((op.flip(), *i, Err(*k))),
                _ => None,
            };
            if let Some((op, a, b)) = lit {
                for o in [op, op.negate()] {
                    if !out.contains(&(o, a, b)) {
                        out.push((o, a, b));
                    }
                }
            }
        };
        self.walk(&mut |p| match p {
            Pat::Cmp(op, a, b) => add(*op, a, b),
            Pat::Dec(arms) => {
                for (op, l, r) in arms.iter().flat_map(|(_, d)| d.iter().flatten()) {
                    add(*op, l, r);
                }
            }
            _ => {}
        });
        out
    }

    /// The pattern's conditions as DNFs over leaf/constant literals (leaf first): every decider
    /// arm's whole DNF and each of its terms, and every comparison alone.
    pub fn dnfs(&self) -> Vec<Vec<Vec<(CmpOp, usize, Result<usize, i32>)>>> {
        let lit = |op: CmpOp, a: &Pat, b: &Pat| match (a, b) {
            (Pat::X(i), Pat::X(j)) => Some((op, *i, Ok(*j))),
            (Pat::X(i), Pat::K(k)) => Some((op, *i, Err(*k))),
            (Pat::K(k), Pat::X(i)) => Some((op.flip(), *i, Err(*k))),
            _ => None,
        };
        let mut out: Vec<Vec<Vec<(CmpOp, usize, Result<usize, i32>)>>> = Vec::new();
        let mut push = |d: Vec<Vec<(CmpOp, usize, Result<usize, i32>)>>| {
            if !out.contains(&d) {
                out.push(d);
            }
        };
        self.walk(&mut |p| match p {
            Pat::Cmp(op, a, b) => {
                if let Some(l) = lit(*op, a, b) {
                    push(vec![vec![l]]);
                }
            }
            Pat::Dec(arms) => {
                for (_, d) in arms {
                    let terms: Option<Vec<Vec<_>>> = d.iter().map(|t| t.iter().map(|(op, a, b)| lit(*op, a, b)).collect()).collect();
                    if let Some(terms) = terms {
                        for t in &terms {
                            push(vec![t.clone()]);
                        }
                        push(terms);
                    }
                }
            }
            _ => {}
        });
        out
    }

    /// Pairs of leaves used as the two conditions of one select (`t`, `f`): complementary
    /// booleans in the IR, so test vectors keep them so.
    pub fn complements(&self) -> Vec<(usize, usize)> {
        let mut out = Vec::new();
        self.walk(&mut |p| {
            if let Pat::Mux(t, f, _, _) = p {
                if let (Pat::X(i), Pat::X(j)) = (&**t, &**f) {
                    out.push((*i, *j));
                }
            }
        });
        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_and_evaluates() {
        let min = Pat::parse("(mux (lt x0 x1) (ge x0 x1) x0 x1)").unwrap();
        assert_eq!(min.eval(&[3, 5]), 3);
        assert_eq!(min.eval(&[i32::MAX, i32::MIN]), i32::MIN);
        let p = Pat::parse("(add x0 (mux (dec (arm 1 (or (and (lt x1 0) (ge x0 0) (ne x0 0)) (and (ge x1 0) (lt x0 0) (ne x0 0))))) _ x1 0))").unwrap();
        // tmod(-7, 3) = -1 → Python -7 % 3 = 2.
        assert_eq!(p.eval(&[-1, 3]), 2);
        assert_eq!(p.leaves(), 2);
        let d = Pat::parse("(dec (arm 16748544 (or (and (lt x0 20000)))) (arm 1579032 (or (and (ge x0 20000)))))").unwrap();
        assert_eq!(d.eval(&[5]), 16748544);
        assert_eq!(d.consts(), vec![20000, 16748544, 1579032]);
        assert_eq!(Pat::parse("(mux x0 _ x1 0)").unwrap().eval(&[1, 9]), 9);
        assert_eq!(Pat::parse("(sel (eq x0 0) 20 (eq x0 1) 16)").unwrap().eval(&[1]), 16);
    }
}

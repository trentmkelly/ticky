//! Combinator integer semantics, matching Factorio 2.0 exactly (verified in-game, 2.0.77).

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum ArOp {
    Mul,
    Div,
    Add,
    Sub,
    Mod,
    Pow,
    Shl,
    Shr,
    And,
    Or,
    Xor,
}

impl ArOp {
    pub fn apply(self, a: i32, b: i32) -> i32 {
        match self {
            ArOp::Mul => a.wrapping_mul(b),
            ArOp::Add => a.wrapping_add(b),
            ArOp::Sub => a.wrapping_sub(b),
            // Division by zero and MIN / -1 both give 0 in-game.
            ArOp::Div => {
                if b == 0 || (a == i32::MIN && b == -1) {
                    0
                } else {
                    a / b
                }
            }
            ArOp::Mod => {
                if b == 0 || (a == i32::MIN && b == -1) {
                    0
                } else {
                    a % b
                }
            }
            ArOp::Pow => pow(a, b),
            // Shift amounts are masked to 5 bits; >> is arithmetic.
            ArOp::Shl => a.wrapping_shl(b as u32 & 31),
            ArOp::Shr => a.wrapping_shr(b as u32 & 31),
            ArOp::And => a & b,
            ArOp::Or => a | b,
            ArOp::Xor => a ^ b,
        }
    }

    pub fn symbol(self) -> &'static str {
        match self {
            ArOp::Mul => "*",
            ArOp::Div => "/",
            ArOp::Add => "+",
            ArOp::Sub => "-",
            ArOp::Mod => "%",
            ArOp::Pow => "^",
            ArOp::Shl => "<<",
            ArOp::Shr => ">>",
            ArOp::And => "AND",
            ArOp::Or => "OR",
            ArOp::Xor => "XOR",
        }
    }

    pub fn commutative(self) -> bool {
        matches!(self, ArOp::Mul | ArOp::Add | ArOp::And | ArOp::Or | ArOp::Xor)
    }
}

/// Negative exponents behave like a truncated reciprocal: 0 unless the base is ±1.
fn pow(base: i32, exp: i32) -> i32 {
    if exp < 0 {
        return match base {
            1 => 1,
            -1 => {
                if exp & 1 == 1 {
                    -1
                } else {
                    1
                }
            }
            _ => 0,
        };
    }
    let (mut result, mut b, mut e) = (1i32, base, exp as u32);
    while e > 0 {
        if e & 1 == 1 {
            result = result.wrapping_mul(b);
        }
        b = b.wrapping_mul(b);
        e >>= 1;
    }
    result
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum CmpOp {
    Lt,
    Gt,
    Eq,
    Ge,
    Le,
    Ne,
}

impl CmpOp {
    pub fn apply(self, a: i32, b: i32) -> bool {
        match self {
            CmpOp::Lt => a < b,
            CmpOp::Gt => a > b,
            CmpOp::Eq => a == b,
            CmpOp::Ge => a >= b,
            CmpOp::Le => a <= b,
            CmpOp::Ne => a != b,
        }
    }

    /// The comparison with operands swapped: `a < b` ⇔ `b > a`.
    pub fn flip(self) -> CmpOp {
        match self {
            CmpOp::Lt => CmpOp::Gt,
            CmpOp::Gt => CmpOp::Lt,
            CmpOp::Ge => CmpOp::Le,
            CmpOp::Le => CmpOp::Ge,
            c => c,
        }
    }

    pub fn negate(self) -> CmpOp {
        match self {
            CmpOp::Lt => CmpOp::Ge,
            CmpOp::Gt => CmpOp::Le,
            CmpOp::Eq => CmpOp::Ne,
            CmpOp::Ge => CmpOp::Lt,
            CmpOp::Le => CmpOp::Gt,
            CmpOp::Ne => CmpOp::Eq,
        }
    }

    pub fn symbol(self) -> &'static str {
        match self {
            CmpOp::Lt => "<",
            CmpOp::Gt => ">",
            CmpOp::Eq => "=",
            CmpOp::Ge => "≥",
            CmpOp::Le => "≤",
            CmpOp::Ne => "≠",
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const MIN: i32 = i32::MIN;

    /// Every case here was measured in Factorio 2.0.77 (ticky/harness probe).
    #[test]
    fn matches_game() {
        let cases = [
            (ArOp::Div, 7, 0, 0),
            (ArOp::Mod, 7, 0, 0),
            (ArOp::Div, MIN, -1, 0),
            (ArOp::Mod, MIN, -1, 0),
            (ArOp::Div, -7, 2, -3),
            (ArOp::Mod, -7, 2, -1),
            (ArOp::Mod, 7, -2, 1),
            (ArOp::Pow, 2, -1, 0),
            (ArOp::Pow, 0, 0, 1),
            (ArOp::Pow, -2, 3, -8),
            (ArOp::Pow, 3, 40, 689956897),
            (ArOp::Pow, 2, 31, MIN),
            (ArOp::Pow, -1, -1, -1),
            (ArOp::Pow, 1, -5, 1),
            (ArOp::Shl, 1, 31, MIN),
            (ArOp::Shl, 1, 32, 1),
            (ArOp::Shl, 1, 33, 2),
            (ArOp::Shl, 1, -1, MIN),
            (ArOp::Shl, 3, -31, 6),
            (ArOp::Shr, -8, 1, -4),
            (ArOp::Shr, -8, 32, -8),
            (ArOp::Shr, -8, 33, -4),
            (ArOp::Shr, 8, -1, 0),
            (ArOp::Shr, MIN, 31, -1),
            (ArOp::Mul, 65536, 65536, 0),
            (ArOp::Add, i32::MAX, 1, MIN),
            (ArOp::Sub, MIN, 1, i32::MAX),
            (ArOp::And, -1, 12, 12),
            (ArOp::Xor, -1, 5, -6),
        ];
        for (op, a, b, want) in cases {
            assert_eq!(op.apply(a, b), want, "{a} {} {b}", op.symbol());
        }
    }
}

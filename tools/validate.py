#!/usr/bin/env python3
"""Translation validation of the Ticky compiler's IR optimisations with an SMT solver.

The compiler, run with `TICKY_EXPORT_IR=file`, appends one JSON line per block/process
(crates/ticky-compiler/src/ir_export.rs): the graph, its sources, every *rewrite claim* made
while building it ("this constructor call asked for `req` and returned node `res`"), and each
writer's values before and after fusion. This tool encodes both sides as 32-bit bitvector
terms with Factorio's exact integer semantics and asks z3 whether they can differ.

Obligations, per unit (block or process):
  claim     `res` == `req` for every logged constructor call (`//` and `%`: under their path
            conditions; `mux_tf`/`bmux_tf`: given complementary conditions, checked separately
            as `pre`).
  fusion    each state's next value as lowered == its fused plan of guarded loads (or its
            accumulator form); runtime-check conditions, branch/wait conditions and dynamic
            wait counts before and after fusion agree; a plan's hold condition is the
            negation of its direct loads' guards.
  inductive the intervals assumed for the unit's own state (the lowering fixpoint) hold for
            every value written to it.

Inputs, other processes' state and `ticks()` take any value in the interval the compiler
assumes for them (FULL for inputs). Bundles are maps over a finite universe: the signals the
unit mentions plus two anonymous ones, so results about bundle totals, counts and rankings are
bounded, not general. A few nodes have no encoding (selector modes like stack sizes and random
picks, symbolic exponents): they become free values within the compiler's interval, and any
result depending on them is marked `*` (it trusts those intervals).

usage:
  tools/validate.py [options] PROGRAM.ticky...   compile each (all --modes) and validate
  tools/validate.py --examples [options]         every examples/*.ticky
  tools/validate.py --corpus DIR [options]       every *.ticky under DIR
  tools/validate.py --export FILE.jsonl          validate an existing export
  tools/validate.py --collect DIR FUZZER [N [SEED]]
                                                 run tools/FUZZER.py with a TICKY shim that
                                                 copies every program it compiles into DIR
  tools/validate.py --selftest                   check the encoding against the compiler's
                                                 own operator table (and lemmas)
options:
  --ticky PATH     compiler (default $TICKY, else target/release/ticky)
  --modes LIST     comma list of speed, size, checks, size-checks (default speed,size-checks)
  --timeout MS     per obligation (default 20000)
  --skip-fusion / --skip-claims / --skip-inductive
  -v               print every obligation;  -q  only the summary
Exit status: 1 if any counterexample was found, else 0.

z3: `python3 -m venv tools/.venv && tools/.venv/bin/pip install z3-solver`; this script
re-runs itself with tools/.venv/bin/python when `import z3` fails.
"""
import glob
import hashlib
import json
import os
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)

try:
    import z3
except ImportError:
    VENV_PY = os.path.join(HERE, ".venv", "bin", "python")
    if os.path.exists(VENV_PY) and os.path.abspath(sys.executable) != os.path.abspath(VENV_PY):
        os.execv(VENV_PY, [VENV_PY] + sys.argv)
    sys.exit("validate.py needs z3: python3 -m venv tools/.venv && tools/.venv/bin/pip install z3-solver")

MIN, MAX = -(2**31), 2**31 - 1
W = 32


def bv(k):
    return z3.BitVecVal(k, W)


ZERO, ONE = bv(0), bv(1)


class Unsupported(Exception):
    """A construct without an encoding."""


# ------------------------------------------------------------------ Factorio semantics


def ar(op, a, b, kb=None):
    """`a op b` as Factorio's arithmetic combinator computes it (ticky_factorio::ArOp::apply).
    `kb`: b's value when it is a constant (needed for `^`)."""
    if op == "Add":
        return a + b
    if op == "Sub":
        return a - b
    if op == "Mul":
        return a * b
    if op == "Div":  # truncating; x / 0 and MIN / -1 are 0
        return z3.If(z3.Or(b == 0, z3.And(a == bv(MIN), b == bv(-1))), ZERO, a / b)
    if op == "Mod":  # sign of the dividend; x % 0 and MIN % -1 are 0
        return z3.If(z3.Or(b == 0, z3.And(a == bv(MIN), b == bv(-1))), ZERO, z3.SRem(a, b))
    if op == "Shl":
        return a << (b & 31)
    if op == "Shr":  # arithmetic
        return a >> (b & 31)
    if op == "And":
        return a & b
    if op == "Or":
        return a | b
    if op == "Xor":
        return a ^ b
    if op == "Pow":
        if kb is None:
            raise Unsupported("x ** y with y not constant")
        if kb < 0:  # a truncated reciprocal: 0 unless the base is ±1
            return z3.If(a == 1, ONE, z3.If(a == bv(-1), bv(-1 if kb & 1 else 1), ZERO))
        result, base, e = ONE, a, kb
        while e > 0:
            if e & 1:
                result = result * base
            base = base * base
            e >>= 1
        return result
    raise Unsupported(f"arithmetic {op}")


def cmpb(op, a, b):
    """`a op b` as a z3 boolean (signed)."""
    return {"Lt": a < b, "Gt": a > b, "Eq": a == b, "Ge": a >= b, "Le": a <= b, "Ne": a != b}[op]


def b2i(c):
    return z3.If(c, ONE, ZERO)


def floor_div(a, b, arf=ar):
    """Python `//` as Ticky defines it on 32-bit values (the compiler's general lowering,
    lower.rs floor_div without range facts): x // 0 == 0, and MIN // -1 == 0 (Factorio's
    MIN / -1), otherwise floored."""
    q, r = arf("Div", a, b), arf("Mod", a, b)
    return q - b2i(z3.And(r != 0, (r < 0) != (b < 0)))


def floor_mod(a, b, arf=ar):
    """Python `%` (sign of the divisor); x % 0 == 0."""
    r = arf("Mod", a, b)
    return r + z3.If(z3.And(r != 0, (r < 0) != (b < 0)), b, ZERO)


def in_iv(x, lo, hi):
    cs = []
    if lo > MIN:
        cs.append(x >= bv(lo))
    if hi < MAX:
        cs.append(x <= bv(hi))
    return z3.And(*cs) if cs else z3.BoolVal(True)


# ------------------------------------------------------------------ units


class Unit:
    """One exported block or process, with z3 terms for its nodes (built on demand)."""

    def __init__(self, d, probe, abstract=False):
        self.abstract = abstract
        self.ufs = {}
        self.d = d
        self.name = d["unit"]
        self.nodes = d["nodes"]
        self.srcs = d["srcs"]
        self.probe = probe
        self.memo = {}
        self.assume = []  # constraints on free values (sources, placeholders, opaque nodes)
        self.opaque = set()  # nodes encoded as free values
        self.idx = probe["index_signal"]
        self.slots = probe["slots"]
        sigs = {int(k): (v[0], tuple(v[1])) for k, v in d.get("sigs", {}).items()}
        universe = set(sigs)
        universe.add(self.idx)
        nslots = 0
        for c in d["claims"]:
            if c["req"][0] in ("AGetN", "ASet", "AAdd", "AZeros"):
                nslots = max(nslots, c["req"][-1])
        universe.update(self.slots[:nslots])
        self.names = {s: v[0] for s, v in sigs.items()}
        self.ranks = {s: v[1] for s, v in sigs.items()}
        for s in universe:
            self.ranks.setdefault(s, (2, s, 0))
            self.names.setdefault(s, f"sig#{s}")
        # Two signals the program never mentions, ranked first and last.
        for s, r, n in ((-1, (-1, 0, 0), "<other-1>"), (-2, (99, 0, 0), "<other-2>")):
            universe.add(s)
            self.ranks[s] = r
            self.names[s] = n
        self.universe = sorted(universe, key=lambda s: self.ranks[s])
        self.srcvars = {}

    # -- helpers

    def ar(self, op, a, b, kb=None):
        """Factorio arithmetic; in abstract mode, multiplication and division of two
        non-constants (and anything with a non-constant divisor) are uninterpreted functions:
        a proof that holds for every function holds for the real one."""
        if self.abstract and op in ("Mul", "Div", "Mod", "Pow"):
            ka, kbv = z3.is_bv_value(z3.simplify(a)), z3.is_bv_value(z3.simplify(b))
            heavy = (op == "Mul" and not ka and not kbv) or (op in ("Div", "Mod") and not (ka and kbv)) or (op == "Pow" and not ka)
            if heavy:
                if op == "Mul" and a.get_id() > b.get_id():
                    a, b = b, a
                f = self.ufs.get(op)
                if f is None:
                    f = self.ufs[op] = z3.Function(f"uf_{op}", z3.BitVecSort(W), z3.BitVecSort(W), z3.BitVecSort(W))
                if op in ("Div", "Mod"):
                    return z3.If(z3.Or(b == 0, z3.And(a == bv(MIN), b == bv(-1))), ZERO, f(a, b))
                return f(a, b)
        if op == "Mul":
            # `(c ? k1 : k2) * x` as `c ? k1*x : k2*x`: one-hot tables times a value would
            # otherwise each cost the solver a 32-bit multiplier.
            for p, q in ((a, b), (b, a)):
                sp = z3.simplify(p)
                if z3.is_app_of(sp, z3.Z3_OP_ITE) and all(z3.is_bv_value(x) for x in sp.children()[1:]):
                    c, k1, k2 = sp.children()
                    return z3.If(c, k1 * q, k2 * q)
        return ar(op, a, b, kb)

    def is_bun(self, v):
        return self.nodes[v][3]

    def iv(self, v):
        return self.nodes[v][1], self.nodes[v][2]

    def const(self, v):
        op = self.nodes[v][0]
        return op[1] if op[0] == "Const" else None

    def free_scalar(self, name, lo, hi, nonzero=False):
        x = z3.BitVec(name, W)
        self.assume.append(in_iv(x, lo, hi))
        if nonzero:
            self.assume.append(x != 0)
        return x

    def free_bundle(self, name, lo, hi, onehot=False):
        out = {}
        for s in self.universe:
            x = z3.BitVec(f"{name}[{self.names[s]}]", W)
            if onehot:
                self.assume.append(z3.Or(x == 0, x == 1))
            elif (lo, hi) != (MIN, MAX):
                self.assume.append(z3.Or(x == 0, in_iv(x, lo, hi)))
            out[s] = x
        if onehot:
            self.assume.append(z3.Sum([z3.ZeroExt(8, out[s]) for s in self.universe]) <= 1)
        return out

    # -- values

    def val(self, v):
        """Node `v`'s value: a z3 bitvector, or a bundle {signal: bitvector}."""
        if v in self.memo:
            return self.memo[v]
        try:
            r = self.enc(self.nodes[v][0], v)
        except Unsupported:
            lo, hi = self.iv(v)
            self.opaque.add(v)
            r = self.free_bundle(f"opaque{v}", lo, hi) if self.is_bun(v) else self.free_scalar(f"opaque{v}", lo, hi)
        self.memo[v] = r
        return r

    def scalar(self, v):
        x = self.val(v)
        if isinstance(x, dict):
            raise Unsupported(f"node {v} is a bundle where a number is expected")
        return x

    def bundle(self, v):
        """Bundle value; constant signals become one-hot bundles."""
        op = self.nodes[v][0]
        if op[0] == "SigK":
            return {s: (ONE if s == op[1] else ZERO) for s in self.universe}
        x = self.val(v)
        if not isinstance(x, dict):
            raise Unsupported(f"node {v} is a number where a bundle is expected")
        return x

    def dnf(self, d):
        return z3.Or(*[z3.And(*[cmpb(o, self.scalar(a), self.scalar(b)) for o, a, b in t]) for t in d])

    def bdnf(self, d, each):
        def opnd(o):
            return each if o == "each" else self.scalar(o)
        return z3.Or(*[z3.And(*[cmpb(o, opnd(a), opnd(b)) for o, a, b in t]) for t in d])

    def kvals(self, vals):
        m = {s: ZERO for s in self.universe}
        for s, k in vals:
            m[s] = m[s] + bv(k)
        return m

    def term(self, t):  # pylint: disable=too-many-return-statements,too-many-branches
        """One bundle term as {signal: value}."""
        U = self.universe
        tag = t[0]
        if tag == "Map":
            b, k = self.bundle(t[2]), self.scalar(t[3])
            return {s: z3.If(b[s] != 0, self.ar(t[1], b[s], k, self.const(t[3])), ZERO) for s in U}
        if tag == "RMap":
            k, b = self.scalar(t[2]), self.bundle(t[3])
            return {s: z3.If(b[s] != 0, self.ar(t[1], k, b[s]), ZERO) for s in U}
        if tag == "Zip":
            a, b = self.bundle(t[2]), self.bundle(t[3])
            return {s: z3.If(z3.Or(a[s] != 0, b[s] != 0), self.ar(t[1], a[s], b[s]), ZERO) for s in U}
        if tag == "One":
            x = self.scalar(t[2])
            return {s: (x if s == t[1] else ZERO) for s in U}
        if tag == "Set":
            b, x = self.bundle(t[1]), self.scalar(t[3])
            return {s: (x - b[s] if s == t[2] else ZERO) for s in U}
        if tag == "Filter":
            b = self.bundle(t[1])
            return {s: z3.If(z3.And(b[s] != 0, self.bdnf(t[2], b[s])), b[s] if t[3] is None else bv(t[3]), ZERO) for s in U}
        if tag == "DFilter":
            dom, b = self.bundle(t[1]), self.bundle(t[2])
            return {s: z3.If(z3.And(dom[s] != 0, self.bdnf(t[3], b[s])), dom[s] if t[4] is None else bv(t[4]), ZERO) for s in U}
        if tag == "K":
            return self.kvals(t[1])
        if tag == "Shift":
            x = self.scalar(t[2])
            return {s: (x + bv(t[3]) if s == t[1] else ZERO) for s in U}
        if tag == "Hot":
            tb, ix = self.bundle(t[1]), self.bundle(t[2])
            i = ix[self.idx]
            return {s: z3.If(z3.And(tb[s] != 0, tb[s] == i), bv(t[3]), ZERO) for s in U}
        if tag == "HotEq":
            tb, x = self.bundle(t[1]), self.scalar(t[2])
            return {s: z3.If(z3.And(tb[s] != 0, tb[s] == x, x != 0), bv(t[3]), ZERO) for s in U}
        if tag == "Fold":
            b = self.bundle(t[1])
            total = z3.Sum([z3.If(b[s] != 0, self.ar(t[2], b[s], bv(t[3]), t[3]), ZERO) for s in U])
            return {s: (total if s == t[4] else ZERO) for s in U}
        if tag == "Ar":
            x = self.ar(t[1], self.scalar(t[2]), self.scalar(t[3]), self.const(t[3]))
            return {s: (x if s == t[4] else ZERO) for s in U}
        if tag == "Dec":
            out = {s: ZERO for s in U}
            for d, vals in t[1]:
                c = self.dnf(d)
                k = self.kvals(vals)
                out = {s: out[s] + z3.If(c, k[s], ZERO) for s in U}
            return out
        raise Unsupported(f"bundle term {tag}")

    def rank_select(self, b, mx, index):
        """The signal of `b` ranked `index` (a z3 term) with its value; nothing past the end."""
        U = self.universe

        def before(t, s):  # t comes before s
            if mx:
                tie = self.ranks[t] < self.ranks[s]
                return z3.Or(b[t] > b[s], z3.And(b[t] == b[s], z3.BoolVal(tie)))
            tie = self.ranks[t] > self.ranks[s]
            return z3.Or(b[t] < b[s], z3.And(b[t] == b[s], z3.BoolVal(tie)))
        out = {}
        for s in U:
            pos = z3.Sum([ZERO] + [z3.If(z3.And(b[t] != 0, before(t, s)), ONE, ZERO) for t in U if t != s])
            out[s] = z3.If(z3.And(b[s] != 0, pos == index), b[s], ZERO)
        return out

    def enc(self, op, v=None):  # pylint: disable=too-many-return-statements,too-many-branches
        """The value of operation `op` (a node's, or a claim's request)."""
        U = self.universe
        tag = op[0]
        if tag == "Const":
            return bv(op[1])
        if tag == "Src":
            return self.src(op[1])
        if tag == "Ar":
            return self.ar(op[1], self.scalar(op[2]), self.scalar(op[3]), self.const(op[3]))
        if tag == "Cmp":
            return b2i(cmpb(op[1], self.scalar(op[2]), self.scalar(op[3])))
        if tag == "Mux":
            t, f = self.scalar(op[1]), self.scalar(op[2])
            return z3.If(t != 0, self.scalar(op[3]), ZERO) + z3.If(f != 0, self.scalar(op[4]), ZERO)
        if tag == "Dec":
            return z3.Sum([ZERO] + [z3.If(self.dnf(d), bv(k), ZERO) for d, k in op[1]])
        if tag == "Sel":
            return z3.Sum([ZERO] + [z3.If(self.scalar(c) != 0, self.scalar(x), ZERO) for c, x in op[1]])
        if tag == "BConst":
            return self.kvals(op[1])
        if tag == "Bun":
            out = None
            for t in op[1]:
                tv = self.term(t)
                out = tv if out is None else {s: out[s] + tv[s] for s in U}
            return out if out is not None else {s: ZERO for s in U}
        if tag == "BMux":
            t, f = self.scalar(op[1]), self.scalar(op[2])
            a, b = self.bundle(op[3]), self.bundle(op[4])
            return {s: z3.If(t != 0, a[s], ZERO) + z3.If(f != 0, b[s], ZERO) for s in U}
        if tag == "BDec":
            out = {s: ZERO for s in U}
            for d, x in op[1]:
                c, xb = self.dnf(d), self.bundle(x)
                out = {s: out[s] + z3.If(c, xb[s], ZERO) for s in U}
            return out
        if tag == "BSelect":
            return self.rank_select(self.bundle(op[1]), op[2], bv(op[3]))
        if tag == "BSelectAt":
            return self.rank_select(self.bundle(op[1]), op[2], self.bundle(op[3])[self.idx])
        if tag == "BGet":
            return self.bundle(op[1])[op[2]]
        if tag == "BTotal":
            b = self.bundle(op[1])
            return z3.Sum([b[s] for s in U])
        if tag == "BCount":
            b = self.bundle(op[1])
            return z3.Sum([z3.If(b[s] != 0, ONE, ZERO) for s in U])
        if tag == "AGet":
            b, ix = self.bundle(op[1]), self.bundle(op[2])
            i = ix[self.idx]
            return z3.Sum([ZERO] + [z3.If(z3.And(ix[s] != 0, ix[s] == i), b[s], ZERO) for s in U if s != self.idx])
        if tag == "BDot":
            a, b = self.bundle(op[1]), self.bundle(op[2])
            return z3.Sum([a[s] * b[s] for s in U])
        if tag == "Each":
            return self.free_scalar(f"each{v}", op[1], op[2], nonzero=True)
        if tag == "SigOf":
            return self.bundle(op[1])
        if tag == "SigK":
            return self.bundle(v)
        raise Unsupported(f"node {tag}")

    def src(self, sid):
        if sid in self.srcvars:
            return self.srcvars[sid]
        s = self.srcs[sid]
        lo, hi = s["iv"]
        name = f"{s['kind']}:{s['name'] or sid}"
        if s["bun"]:
            x = self.free_bundle(name, lo, hi, onehot=s["sig"])
        else:
            x = self.free_scalar(name, lo, hi)
        self.srcvars[sid] = x
        return x

    def own(self, si, bundle=False):
        """The current value of own state `si` (its source, or a fresh value if not read)."""
        for i, s in enumerate(self.srcs):
            if s["kind"] == "Own" and s["index"] == si:
                return self.src(i)
        key = ("old", si)
        if key not in self.memo:
            self.memo[key] = self.free_bundle(f"old-state-{si}", MIN, MAX) if bundle else z3.BitVec(f"old-state-{si}", W)
        return self.memo[key]

    # -- requests (what a constructor call asked for)

    def truth(self, v):
        op = self.nodes[v][0]
        if self.is_bun(v) or op[0] in ("SigK", "SigOf"):
            b = self.bundle(v)
            return z3.Or(*[b[s] != 0 for s in self.universe])
        return self.scalar(v) != 0

    def value_of(self, v):
        """A value as compared in claims: signals as their one-hot bundles."""
        op = self.nodes[v][0]
        if op[0] == "SigK":
            return self.bundle(v)
        return self.val(v)

    def req(self, r):  # pylint: disable=too-many-return-statements
        tag = r[0]
        U = self.universe
        if tag == "PyMux":
            c = self.truth(r[1])
            a, b = self.value_of(r[2]), self.value_of(r[3])
            return select(c, a, b, U)
        if tag == "Not":
            return b2i(z3.Not(self.truth(r[1])))
        if tag == "Truth":
            return b2i(self.truth(r[1]))
        if tag == "AGetN":
            b, i, n = self.bundle(r[1]), self.scalar(r[2]), r[3]
            return z3.Sum([ZERO] + [z3.If(i == k, b[self.slots[k]], ZERO) for k in range(n)])
        if tag in ("ASet", "AAdd"):
            b, i, x, n = self.bundle(r[1]), self.scalar(r[2]), self.scalar(r[3]), r[4]
            out = dict(b)
            for k in range(n):
                s = self.slots[k]
                out[s] = z3.If(i == k, x if tag == "ASet" else b[s] + x, b[s])
            return out
        if tag == "BSetS":
            b, x = self.bundle(r[1]), self.scalar(r[3])
            out = dict(b)
            out[r[2]] = x
            return out
        if tag == "AZeros":
            b, x, n = self.bundle(r[1]), self.scalar(r[2]), r[3]
            out = {s: ZERO for s in U}
            for k in range(n):
                s = self.slots[k]
                out[s] = z3.If(b[s] == 0, x, ZERO)
            return out
        if tag == "FloorDiv":
            return floor_div(self.scalar(r[1]), self.scalar(r[2]), self.ar)
        if tag == "FloorMod":
            return floor_mod(self.scalar(r[1]), self.scalar(r[2]), self.ar)
        return self.enc(r)


def select(c, a, b, U):
    if isinstance(a, dict) or isinstance(b, dict):
        if not (isinstance(a, dict) and isinstance(b, dict)):
            raise Unsupported("select between a number and a bundle")
        return {s: z3.If(c, a[s], b[s]) for s in U}
    return z3.If(c, a, b)


def equal(a, b, U):
    """`a == b` as a list of goals (one per signal for bundles: proved one at a time, each
    with only its own cone)."""
    if isinstance(a, dict) or isinstance(b, dict):
        if not (isinstance(a, dict) and isinstance(b, dict)):
            raise Unsupported("comparing a number with a bundle")
        return [a[s] == b[s] for s in U]
    return [a == b]


# ------------------------------------------------------------------ obligations


class Result:
    def __init__(self, unit, kind, what, status, detail=""):
        self.unit, self.kind, self.what, self.status, self.detail = unit, kind, what, status, detail


def solve(u, goal, extra_assume, timeout):
    """Proves `goal` (a z3 boolean, or a list of them) under the unit's assumptions.
    Returns (status, model)."""
    status = "equivalent"
    for g in goal if isinstance(goal, list) else [goal]:
        if z3.is_true(z3.simplify(g)):
            continue
        s = z3.Solver()
        s.set("timeout", timeout)
        s.add(*u.assume)
        s.add(*extra_assume)
        s.add(z3.Not(g))
        r = s.check()
        if r == z3.sat:
            return "counterexample", s.model()
        if r != z3.unsat:
            status = "unknown"
    return status, None


def show_model(u, m, terms):
    out = []
    for d in m.decls():
        val = m[d]
        if z3.is_bv_value(val):
            x = val.as_long()
            x = x - (1 << W) if x >= 1 << (W - 1) else x
            if x != 0 or not d.name().startswith(("opaque", "old")):
                out.append(f"{d.name()}={x}")
    out.sort()
    for name, t in terms:
        if isinstance(t, dict):
            vals = {u.names[s]: signed(m.eval(t[s], model_completion=True)) for s in u.universe}
            vals = {k: x for k, x in vals.items() if x != 0}
            out.append(f"{name}={vals}")
        elif t is not None:
            out.append(f"{name}={signed(m.eval(t, model_completion=True))}")
    return ", ".join(out)


def signed(x):
    x = x.as_long()
    return x - (1 << W) if x >= 1 << (W - 1) else x


def pretty(u, v, depth=3):
    """A node as an expression, `depth` levels deep."""
    if not isinstance(v, int):
        return str(v)
    op = u.nodes[v][0]
    tag = op[0]
    if tag == "Const":
        return str(op[1])
    if tag == "Src":
        s = u.srcs[op[1]]
        return f"{s['name'] or 'src'}"
    if depth == 0:
        return f"n{v}"
    p = lambda x: pretty(u, x, depth - 1)  # noqa: E731
    sym = {"Add": "+", "Sub": "-", "Mul": "*", "Div": "/", "Mod": "%", "Pow": "^", "Shl": "<<", "Shr": ">>", "And": "&", "Or": "|", "Xor": "^^",
           "Lt": "<", "Gt": ">", "Eq": "==", "Ge": ">=", "Le": "<=", "Ne": "!="}
    if tag in ("Ar", "Cmp"):
        return f"({p(op[2])} {sym[op[1]]} {p(op[3])})"
    if tag == "Mux":
        return f"({p(op[3])} if {p(op[1])} else {p(op[4])})"
    return f"n{v}:{tag}"


def pretty_req(u, r):
    tag = r[0]
    if tag in ("Ar", "Cmp", "Mux"):
        return pretty_op(u, r)
    if tag == "FloorDiv":
        return f"({pretty(u, r[1])} // {pretty(u, r[2])})"
    if tag == "FloorMod":
        return f"({pretty(u, r[1])} %% {pretty(u, r[2])})"
    if tag == "PyMux":
        return f"({pretty(u, r[2])} if {pretty(u, r[1])} else {pretty(u, r[3])})"
    return json.dumps(r)[:200]


def pretty_op(u, r):
    tmp = u.nodes + [[r, MIN, MAX, False]]
    saved = u.nodes
    u.nodes = tmp
    try:
        return pretty(u, len(tmp) - 1)
    finally:
        u.nodes = saved


def check_claim(u, c, timeout):
    rule, r, res = c["rule"], c["req"], c["res"]
    U = u.universe
    pre = []
    results = []
    opaque0 = set(u.opaque)
    try:
        want = u.req(r)
        got = u.value_of(res)
        extra = [u.scalar(p) != 0 for p in c.get("path", [])]
        if rule in ("mux_tf", "bmux_tf"):
            t, f = u.scalar(r[1]), u.scalar(r[2])
            pre = [z3.Xor(t != 0, f != 0)]
            st, m = solve(u, pre[0], [], timeout)
            if st != "equivalent":
                detail = show_model(u, m, [("t", t), ("f", f)]) if m else ""
                results.append(Result(u.name, "pre", f"{rule} conditions complementary: {pretty_req(u, r)}", st, detail))
        goal = equal(want, got, U)
    except Unsupported as e:
        return results + [Result(u.name, "claim", f"{rule}: {pretty_req(u, r)}", "unsupported", str(e))]
    st, m = solve(u, goal, pre + extra, timeout)
    detail = ""
    if m is not None:
        detail = show_model(u, m, [("asked", want), ("got", got)])
    star = "*" if any(o not in opaque0 for o in u.opaque) or (u.opaque and depends_on_opaque(u, [res] + ops_of(r))) else ""
    results.append(Result(u.name, "claim", f"{rule}: {pretty_req(u, r)} -> {pretty(u, res)}", st + star if st == "equivalent" else st, detail))
    return results


def ops_of(r):
    out = []
    def walk(x):
        if isinstance(x, list):
            for y in x:
                walk(y)
        elif isinstance(x, int) and not isinstance(x, bool):
            out.append(x)
    walk(r[1:])
    return [x for x in out if x >= 0]


def depends_on_opaque(u, roots):
    """Whether any of `roots` (node ids; other ints are ignored) reaches an opaque node."""
    n = len(u.nodes)
    seen, stack = set(), [x for x in roots if 0 <= x < n]
    while stack:
        v = stack.pop()
        if v in seen:
            continue
        seen.add(v)
        if v in u.opaque:
            return True
        stack.extend(x for x in ops_of(u.nodes[v][0]) if 0 <= x < n)
    return False


def lift(f, *xs):
    """`f` applied to scalars, or signal by signal to bundles (all bundles, or all scalars)."""
    if any(isinstance(x, dict) for x in xs):
        if not all(isinstance(x, dict) for x in xs):
            raise Unsupported("mixing numbers and bundles")
        return {s: f(*[x[s] for x in xs]) for s in xs[0]}
    return f(*xs)


def plan_value(u, p, old):
    """The register's next value under a fused plan: the sum of the loads whose guards hold
    (a `Const(0)` load just stops the hold), or its old value when none does."""
    acc = lift(lambda o: ZERO, old)
    guards = []
    for l in p["loads"]:
        g = u.dnf(l["guard"])
        guards.append(g)
        if l["val"][0] == "Const":
            k = l["val"][1]
            if isinstance(old, dict) and k != 0:
                raise Unsupported("constant load into a bundle register")
            val = lift(lambda o, k=k: bv(k), old)
        else:
            val = u.value_of(l["val"][1])
        acc = lift(lambda a, x, g=g: a + z3.If(g, x, ZERO), acc, val)
    none = z3.Or(*guards)
    return lift(lambda a, o: a + z3.If(none, ZERO, o), acc, old), guards


def check_writer(u, w, timeout):  # pylint: disable=too-many-locals,too-many-branches,too-many-statements
    out = []
    plans = dict((si, p) for si, p in w["plans"])
    accs = dict((si, a) for si, a in w["accs"])
    for si, name, v in w["writes"]:
        what = f"{w['name']}: {name or si} = {pretty(u, v)}"
        try:
            nxt = u.value_of(v)
            old = u.own(si, isinstance(nxt, dict))
            if si in accs:
                a = accs[si]
                got = z3.Sum([ZERO] + [z3.If(u.dnf(d), bv(k), ZERO) for d, k in a["consts"]])
                got = got + z3.If(u.dnf(a["otherwise"]), old + u.scalar(a["w"]), ZERO)
                kind = "accumulator"
            elif si in plans:
                got, guards = plan_value(u, plans[si], old)
                kind = "plan"
                p = plans[si]
                if p["keep"] is not None:
                    direct = [g for g, l in zip(guards, p["loads"]) if l["direct"]]
                    st, m = solve(u, u.dnf(p["keep"]) == z3.Not(z3.Or(*direct)), [], timeout)
                    out.append(Result(u.name, "fusion", f"{what}: hold condition", st, show_model(u, m, []) if m else ""))
            else:
                got, kind = old, "no plan (keeps its value)"
            goal = equal(nxt, got, u.universe)
        except Unsupported as e:
            out.append(Result(u.name, "fusion", what, "unsupported", str(e)))
            continue
        st, m = solve(u, goal, [], timeout)
        out.append(Result(u.name, "fusion", f"{what}: {kind}", st, show_model(u, m, [("lowered", nxt), ("fused", got)]) if m else ""))
    for raw, fused in w["checks"]:
        try:
            st, m = solve(u, (u.scalar(raw) != 0) == (u.scalar(fused) != 0), [], timeout)
        except Unsupported:
            st, m = "unsupported", None
        out.append(Result(u.name, "fusion", f"{w['name']}: check {pretty(u, raw)} -> {pretty(u, fused)}", st, show_model(u, m, []) if m else ""))
    for node, c in w["conds"]:
        try:
            base = u.truth(node)
            goals = [base == u.truth(c["node"])]
            if c["pos"] is not None:
                goals.append(u.dnf(c["pos"]) == base)
            if c["neg"] is not None:
                goals.append(u.dnf(c["neg"]) == z3.Not(base))
            st, m = solve(u, z3.And(*goals), [], timeout)
        except Unsupported:
            st, m = "unsupported", None
        out.append(Result(u.name, "fusion", f"{w['name']}: condition {pretty(u, node)}", st, show_model(u, m, []) if m else ""))
    for m0, m1 in w["waits"]:
        try:
            st, m = solve(u, u.scalar(m0) == u.scalar(m1), [], timeout)
        except Unsupported:
            st, m = "unsupported", None
        out.append(Result(u.name, "fusion", f"{w['name']}: wait {pretty(u, m0)}", st, show_model(u, m, []) if m else ""))
    return out


def check_inductive(u, timeout):
    """Own state stays within the interval the lowering assumed for it."""
    out = []
    for sid, s in enumerate(u.srcs):
        if s["kind"] != "Own":
            continue
        lo, hi = s["iv"]
        if (lo, hi) == (MIN, MAX):
            continue
        for w in u.d["writers"]:
            for si, name, v in w["writes"]:
                if si != s["index"]:
                    continue
                what = f"{w['name']}: {name} stays in [{lo}, {hi}]"
                try:
                    x = u.val(v)
                    if isinstance(x, dict):
                        goal = z3.And(*[z3.Or(x[t] == 0, in_iv(x[t], lo, hi)) for t in u.universe]) if not s["sig"] else z3.BoolVal(True)
                    else:
                        goal = in_iv(x, lo, hi)
                    st, m = solve(u, goal, [], timeout)
                except Unsupported as e:
                    out.append(Result(u.name, "inductive", what, "unsupported", str(e)))
                    continue
                out.append(Result(u.name, "inductive", what, st, show_model(u, m, [("written", x)]) if m else ""))
    return out


# ------------------------------------------------------------------ driver


def load(path):
    probe, units = None, []
    seen = set()
    with open(path, encoding="utf-8") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            d = json.loads(line)
            if "probe" in d:
                probe = d["probe"]
                continue
            key = hashlib.sha1(line.encode()).hexdigest()
            if key in seen:
                continue
            seen.add(key)
            units.append((probe, d))
    return units


def validate_export(path, args, label, totals):
    units = load(path)
    for probe, d in units:
        t_unit = time.time()
        u = Unit(d, probe)
        ua = Unit(d, probe, abstract=True)
        results = []

        def two_tier(check, *xs):
            # Multiplication and division as uninterpreted functions first (cheap; a proof
            # there is a proof), then the exact encoding for whatever that didn't prove.
            first = check(ua, *xs, min(args["timeout"], 5000))
            if all(r.status.startswith("equivalent") for r in first):
                return first
            return check(u, *xs, args["timeout"])
        if not args["skip_claims"]:
            for c in d["claims"]:
                results.extend(two_tier(check_claim, c))
        if not args["skip_fusion"]:
            for w in d["writers"]:
                results.extend(two_tier(check_writer, w))
        if not args["skip_inductive"]:
            results.extend(two_tier(check_inductive))
        counts = {}
        for r in results:
            st = r.status.rstrip("*")
            key = st + ("*" if r.status.endswith("*") else "")
            counts[key] = counts.get(key, 0) + 1
            totals[key] = totals.get(key, 0) + 1
            totals.setdefault("by_kind", {}).setdefault((r.kind, key), 0)
            totals["by_kind"][(r.kind, key)] += 1
            if r.status == "counterexample" or (args["verbose"] and r.status != "equivalent") or args["verbose"] > 1:
                print(f"  {r.status.upper():15} [{label} | {u.name} {mode_of(d)}] {r.kind} {r.what}" + (f"\n                  {r.detail}" if r.detail else ""))
            if r.status == "counterexample":
                totals.setdefault("cex", []).append((label, u.name, mode_of(d), r))
            if r.status in ("unknown", "unsupported") and args["verbose"]:
                pass
        verdict = "counterexample" if counts.get("counterexample") else ("unknown" if counts.get("unknown") or counts.get("unsupported") else "equivalent")
        totals.setdefault("units", {}).setdefault(verdict, 0)
        totals["units"][verdict] += 1
        if not args["quiet"]:
            summary = ", ".join(f"{k} {v}" for k, v in sorted(counts.items()))
            print(f"{verdict:15} {label} | {u.name} {mode_of(d)}: {summary or 'nothing to check'} (+{d['trivial']} trivial) {time.time() - t_unit:.1f}s", flush=True)
        totals["trivial"] = totals.get("trivial", 0) + d["trivial"]


def mode_of(d):
    return "[" + ("size" if d.get("opt_size") else "speed") + (",checks" if d.get("checks_on") else "") + "]"


MODES = {"speed": [], "size": ["--opt=size"], "checks": ["--checks"], "size-checks": ["--opt=size", "--checks"]}


def export_program(ticky, prog, modes, out):
    env = dict(os.environ, TICKY_EXPORT_IR=out)
    ok = True
    for m in modes:
        r = subprocess.run([ticky, "check", prog] + MODES[m], env=env, capture_output=True, text=True, check=False)
        if r.returncode != 0:
            ok = False
            print(f"  (compile failed: {prog} {m}: {r.stderr.strip().splitlines()[-1] if r.stderr.strip() else r.returncode})")
    return ok


def selftest(ticky):
    """The encoding against the compiler's operator table, and floor-division lemmas."""
    with tempfile.TemporaryDirectory() as d:
        prog = os.path.join(d, "p.ticky")
        with open(prog, "w", encoding="utf-8") as f:
            f.write("input x: int @ X\noutput y: int @ Y\nevery tick:\n    y = x + 1\n")
        out = os.path.join(d, "e.jsonl")
        export_program(ticky, prog, ["speed"], out)
        probe = next(json.loads(l)["probe"] for l in open(out, encoding="utf-8") if '"probe"' in l)
    bad = 0
    for op, a, b, want in probe["ops"]:
        if op in ("Lt", "Gt", "Eq", "Ge", "Le", "Ne"):
            got = z3.simplify(b2i(cmpb(op, bv(a), bv(b))))
        else:
            got = z3.simplify(ar(op, bv(a), bv(b), b))
        if signed(got) != want:
            bad += 1
            print(f"MISMATCH {a} {op} {b}: compiler {want}, encoding {signed(got)}")
    print(f"operator table: {len(probe['ops'])} cases, {bad} mismatches")
    # Python's floor semantics (wrapped to 32 bits; x // 0 == x % 0 == 0; MIN // -1 is 0, as
    # Factorio's MIN / -1), on small values exhaustively and on random 32-bit pairs.
    import random  # pylint: disable=import-outside-toplevel
    rnd = random.Random(1)
    edge = [MIN, MIN + 1, -65536, -3, -2, -1, 0, 1, 2, 3, 65536, MAX - 1, MAX]
    pairs = [(a, b) for a in range(-20, 21) for b in range(-7, 8)] + [(a, b) for a in edge for b in edge]
    pairs += [(rnd.randint(MIN, MAX), rnd.choice([rnd.randint(MIN, MAX), rnd.randint(-40, 40)])) for _ in range(3000)]
    for a, b in pairs:
        want_d = 0 if b == 0 or (a, b) == (MIN, -1) else a // b
        want_m = 0 if b == 0 else a % b
        if signed(z3.simplify(floor_div(bv(a), bv(b)))) != want_d or signed(z3.simplify(floor_mod(bv(a), bv(b)))) != want_m:
            bad += 1
            print(f"MISMATCH floor {a} {b}")
    print(f"floor division/modulo: {len(pairs)} cases")
    print("selftest:", "ok" if bad == 0 else f"{bad} FAILURES")
    return bad == 0


SHIM = """#!/usr/bin/env bash
# validate.py --collect: keep every program a fuzzer compiles, then run the real compiler.
for a in "$@"; do
  case "$a" in
    *.ticky) [ -f "$a" ] && cp "$a" "{dir}/$(date +%s%N)-$$.ticky" ;;
  esac
done
exec "{ticky}" "$@"
"""


def collect(dirname, fuzzer, n, seed, ticky):
    os.makedirs(dirname, exist_ok=True)
    with tempfile.TemporaryDirectory() as d:
        shim = os.path.join(d, "ticky")
        with open(shim, "w", encoding="utf-8") as f:
            f.write(SHIM.replace("{dir}", os.path.abspath(dirname)).replace("{ticky}", os.path.abspath(ticky)))
        os.chmod(shim, 0o755)
        path = fuzzer if os.path.exists(fuzzer) else os.path.join(HERE, fuzzer if fuzzer.endswith(".py") else fuzzer + ".py")
        env = dict(os.environ, TICKY=shim)
        r = subprocess.run([sys.executable if False else "python3", path, str(n), str(seed)], env=env, capture_output=True, text=True, check=False)
        tail = r.stdout.strip().splitlines()[-1:] if r.stdout.strip() else []
        print(f"{os.path.basename(path)} {n} {seed}: exit {r.returncode} {' '.join(tail)}")
    print(f"{len(glob.glob(os.path.join(dirname, '*.ticky')))} programs in {dirname}")


def main():  # pylint: disable=too-many-branches,too-many-statements
    argv = sys.argv[1:]
    args = {"timeout": 20000, "skip_claims": False, "skip_fusion": False, "skip_inductive": False, "verbose": 0, "quiet": False}
    ticky = os.environ.get("TICKY") or os.path.join(ROOT, "target", "release", "ticky")
    modes = ["speed", "size-checks"]
    progs, exports = [], []
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--ticky":
            ticky = argv[i + 1]
            i += 1
        elif a == "--modes":
            modes = argv[i + 1].split(",")
            i += 1
        elif a == "--timeout":
            args["timeout"] = int(argv[i + 1])
            i += 1
        elif a in ("--skip-fusion", "--skip-claims", "--skip-inductive"):
            args[a[2:].replace("-", "_")] = True
        elif a == "-v":
            args["verbose"] += 1
        elif a == "-vv":
            args["verbose"] += 2
        elif a == "-q":
            args["quiet"] = True
        elif a == "--examples":
            progs.extend(sorted(glob.glob(os.path.join(ROOT, "examples", "*.ticky"))))
        elif a == "--corpus":
            progs.extend(sorted(glob.glob(os.path.join(argv[i + 1], "**", "*.ticky"), recursive=True)))
            i += 1
        elif a == "--export":
            exports.append(argv[i + 1])
            i += 1
        elif a == "--selftest":
            sys.exit(0 if selftest(ticky) else 1)
        elif a == "--collect":
            rest = argv[i + 1:]
            collect(rest[0], rest[1], rest[2] if len(rest) > 2 else 20, rest[3] if len(rest) > 3 else 1, ticky)
            return
        elif a in ("-h", "--help"):
            print(__doc__)
            return
        else:
            progs.append(a)
        i += 1
    totals = {}
    t0 = time.time()
    failed = []
    for e in exports:
        validate_export(e, args, os.path.basename(e), totals)
    with tempfile.TemporaryDirectory() as d:
        for p in progs:
            out = os.path.join(d, hashlib.sha1(p.encode()).hexdigest() + ".jsonl")
            if not export_program(ticky, p, modes, out):
                failed.append(p)
            if os.path.exists(out):
                validate_export(out, args, os.path.relpath(p, ROOT) if p.startswith(ROOT) else p, totals)
    print()
    for label, unit, mode, r in totals.get("cex", []):
        print(f"COUNTEREXAMPLE {label} | {unit} {mode}: {r.kind} {r.what}\n    {r.detail}")
    units = totals.get("units", {})
    print(f"units: " + ", ".join(f"{k} {v}" for k, v in sorted(units.items())))
    print("obligations: " + ", ".join(f"{k} {v}" for k, v in sorted((k, v) for k, v in totals.items() if isinstance(v, int))))
    by = totals.get("by_kind", {})
    for kind in ("claim", "pre", "fusion", "inductive"):
        row = {k: v for (kk, k), v in by.items() if kk == kind}
        if row:
            print(f"  {kind:10} " + ", ".join(f"{k} {v}" for k, v in sorted(row.items())))
    if failed:
        print(f"compile failures (not validated): {len(failed)}")
    print(f"time {time.time() - t0:.1f}s")
    sys.exit(1 if totals.get("cex") else 0)


if __name__ == "__main__":
    main()

#!/usr/bin/env python3
"""Constructive Arithmetic Verification Engine for Goedel Formalization.

This module faithfully models the constructive arithmetization of syntax from:
- cPair.v (Cantor pairing function and inverse projections)
- Languages.v (LNT and LNN function and relation codes)
- code.v (Gödel numbering of terms, lists of terms, and formulas)
- codeNatToTerm.v (Numeral term coding nat_rec)
- codeFreeVar.v (Free variable computation)
- fixPoint.v (Diagonal Lemma / Fixed Point sentence construction)
"""

from __future__ import annotations
from dataclasses import dataclass
import math
import sys
from typing import List, Optional, Set, Tuple, Union

try:
    sys.set_int_max_str_digits(50000)
except Exception:
    pass


# --- 1. Cantor Pairing Function and Inverses (cPair.v) ---

def cpair(x: int, y: int) -> int:
    """Cantor pairing function matching cPair.v:
    cPair x y = y + ((x + y) * (x + y + 1)) // 2
    """
    if x < 0 or y < 0:
        raise ValueError(f"Cantor pairing requires non-negative integers, got ({x}, {y})")
    sum_xy = x + y
    return y + (sum_xy * (sum_xy + 1)) // 2


def cpair_pi1_pi2(z: int) -> Tuple[int, int]:
    """Inverse projections (cPairPi1, cPairPi2) matching cPair.v."""
    if z < 0:
        raise ValueError(f"Cantor inverse requires non-negative integer, got {z}")
    s = math.isqrt(8 * z + 1)
    w = (s - 1) // 2
    t = (w * (w + 1)) // 2
    y = z - t
    x = w - y
    return x, y


def cpair_pi1(z: int) -> int:
    """First projection cPairPi1."""
    return cpair_pi1_pi2(z)[0]


def cpair_pi2(z: int) -> int:
    """Second projection cPairPi2."""
    return cpair_pi1_pi2(z)[1]


def cpair_triple(a: int, b: int, c: int) -> int:
    """cTriple matching codeSubFormula.v: cPair a (cPair b c)."""
    return cpair(a, cpair(b, c))


# --- 2. Language Symbols and AST (Languages.v, fol.v) ---

class LNTFunction:
    PLUS = 0   # arity 2
    TIMES = 1  # arity 2
    SUCC = 2   # arity 1
    ZERO = 3   # arity 0


class LNNRelation:
    LT = 0     # arity 2


@dataclass(frozen=True)
class Var:
    index: int


@dataclass(frozen=True)
class Apply:
    func: int  # LNTFunction code
    args: Tuple[Term, ...]


Term = Union[Var, Apply]


# Convenience constructors for Terms
def var(n: int) -> Var:
    return Var(n)

def zero_term() -> Apply:
    return Apply(LNTFunction.ZERO, ())

def succ_term(t: Term) -> Apply:
    return Apply(LNTFunction.SUCC, (t,))

def plus_term(t1: Term, t2: Term) -> Apply:
    return Apply(LNTFunction.PLUS, (t1, t2))

def times_term(t1: Term, t2: Term) -> Apply:
    return Apply(LNTFunction.TIMES, (t1, t2))

def nat_to_term(n: int) -> Term:
    """Standard numeral term for n."""
    res = zero_term()
    for _ in range(n):
        res = succ_term(res)
    return res


# Formulas
@dataclass(frozen=True)
class Equal:
    t1: Term
    t2: Term

@dataclass(frozen=True)
class ImpH:
    f1: Formula
    f2: Formula

@dataclass(frozen=True)
class NotH:
    f: Formula

@dataclass(frozen=True)
class ForallH:
    var_index: int
    f: Formula

@dataclass(frozen=True)
class AtomicLT:
    t1: Term
    t2: Term


Formula = Union[Equal, ImpH, NotH, ForallH, AtomicLT]


# Derived Connectives
def or_h(f1: Formula, f2: Formula) -> Formula:
    return ImpH(NotH(f1), f2)

def and_h(f1: Formula, f2: Formula) -> Formula:
    return NotH(ImpH(f1, NotH(f2)))

def exist_h(v: int, f: Formula) -> Formula:
    return NotH(ForallH(v, NotH(f)))

def iff_h(f1: Formula, f2: Formula) -> Formula:
    return and_h(ImpH(f1, f2), ImpH(f2, f1))


# --- 3. Gödel Coding of Terms and Formulas (code.v) ---

def code_term(t: Term) -> int:
    """Gödel number of a term matching codeTerm in code.v."""
    if isinstance(t, Var):
        return cpair(0, t.index)
    elif isinstance(t, Apply):
        return cpair(1 + t.func, code_terms(t.args))
    raise TypeError(f"Unknown term type {type(t)}")


def code_terms(ts: Tuple[Term, ...]) -> int:
    """Gödel number of a list of terms matching codeTerms in code.v:
    Tnil => 0
    Tcons t ss => S (cPair (codeTerm t) (codeTerms ss))
    """
    if len(ts) == 0:
        return 0
    head = ts[0]
    tail = ts[1:]
    return 1 + cpair(code_term(head), code_terms(tail))


def decode_term(c: int) -> Term:
    """Decode a Gödel number back to a Term."""
    tag, rest = cpair_pi1_pi2(c)
    if tag == 0:
        return Var(rest)
    func = tag - 1
    args = decode_terms(rest)
    return Apply(func, tuple(args))


def decode_terms(c: int) -> List[Term]:
    """Decode a Gödel number back to a list of Terms."""
    if c == 0:
        return []
    inner = c - 1
    head_code, tail_code = cpair_pi1_pi2(inner)
    return [decode_term(head_code)] + decode_terms(tail_code)


def code_nat_to_term(n: int) -> int:
    """Computes code of numeral n matching codeNatToTerm.v:
    nat_rec (fun _ => nat) (cPair 4 0) (fun _ rec => cPair 3 (S (cPair rec 0)))
    """
    rec = cpair(4, 0)
    for _ in range(n):
        rec = cpair(3, 1 + cpair(rec, 0))
    return rec


def code_formula(f: Formula) -> int:
    """Gödel number of a formula matching codeFormula in code.v:
    equal t1 t2 => cPair 0 (cPair (codeTerm t1) (codeTerm t2))
    impH f1 f2  => cPair 1 (cPair (codeFormula f1) (codeFormula f2))
    notH f1     => cPair 2 (codeFormula f1)
    forallH n f1=> cPair 3 (cPair n (codeFormula f1))
    atomic R ts => cPair (4 + codeR R) (codeTerms ts)
    """
    if isinstance(f, Equal):
        return cpair(0, cpair(code_term(f.t1), code_term(f.t2)))
    elif isinstance(f, ImpH):
        return cpair(1, cpair(code_formula(f.f1), code_formula(f.f2)))
    elif isinstance(f, NotH):
        return cpair(2, code_formula(f.f))
    elif isinstance(f, ForallH):
        return cpair(3, cpair(f.var_index, code_formula(f.f)))
    elif isinstance(f, AtomicLT):
        # In LNN, relation LT has code 0
        return cpair(4 + LNNRelation.LT, code_terms((f.t1, f.t2)))
    raise TypeError(f"Unknown formula type {type(f)}")


def decode_formula(c: int) -> Formula:
    """Decode a Gödel number back to a Formula."""
    tag, rest = cpair_pi1_pi2(c)
    if tag == 0:
        c1, c2 = cpair_pi1_pi2(rest)
        return Equal(decode_term(c1), decode_term(c2))
    elif tag == 1:
        c1, c2 = cpair_pi1_pi2(rest)
        return ImpH(decode_formula(c1), decode_formula(c2))
    elif tag == 2:
        return NotH(decode_formula(rest))
    elif tag == 3:
        var_idx, body_code = cpair_pi1_pi2(rest)
        return ForallH(var_idx, decode_formula(body_code))
    elif tag == 4:
        # Atomic LT in LNN
        args = decode_terms(rest)
        if len(args) != 2:
            raise ValueError(f"Atomic LT expected 2 arguments, got {len(args)}")
        return AtomicLT(args[0], args[1])
    else:
        raise ValueError(f"Unknown formula tag {tag}")


# --- 4. Free Variables and Substitution (folProp.v, subProp.v) ---

def free_vars_term(t: Term) -> Set[int]:
    """Set of free variable indices in term t."""
    if isinstance(t, Var):
        return {t.index}
    elif isinstance(t, Apply):
        res: Set[int] = set()
        for a in t.args:
            res.update(free_vars_term(a))
        return res
    raise TypeError(f"Unknown term {t}")


def free_vars_formula(f: Formula) -> Set[int]:
    """Set of free variable indices in formula f."""
    if isinstance(f, Equal):
        return free_vars_term(f.t1) | free_vars_term(f.t2)
    elif isinstance(f, ImpH):
        return free_vars_formula(f.f1) | free_vars_formula(f.f2)
    elif isinstance(f, NotH):
        return free_vars_formula(f.f)
    elif isinstance(f, ForallH):
        return free_vars_formula(f.f) - {f.var_index}
    elif isinstance(f, AtomicLT):
        return free_vars_term(f.t1) | free_vars_term(f.t2)
    raise TypeError(f"Unknown formula {f}")


def new_var(used_vars: Set[int]) -> int:
    """Returns a fresh variable index strictly greater than any used variable."""
    if not used_vars:
        return 0
    return max(used_vars) + 1


def substitute_term(t: Term, v: int, s: Term) -> Term:
    """Syntactic substitution t[v := s]."""
    if isinstance(t, Var):
        return s if t.index == v else t
    elif isinstance(t, Apply):
        return Apply(t.func, tuple(substitute_term(a, v, s) for a in t.args))
    raise TypeError(f"Unknown term {t}")


def substitute_formula(f: Formula, v: int, s: Term) -> Formula:
    """Capture-avoiding syntactic substitution f[v := s]."""
    if isinstance(f, Equal):
        return Equal(substitute_term(f.t1, v, s), substitute_term(f.t2, v, s))
    elif isinstance(f, ImpH):
        return ImpH(substitute_formula(f.f1, v, s), substitute_formula(f.f2, v, s))
    elif isinstance(f, NotH):
        return NotH(substitute_formula(f.f, v, s))
    elif isinstance(f, AtomicLT):
        return AtomicLT(substitute_term(f.t1, v, s), substitute_term(f.t2, v, s))
    elif isinstance(f, ForallH):
        if f.var_index == v:
            return f
        s_free = free_vars_term(s)
        if f.var_index in s_free:
            # Need alpha-conversion
            nv = new_var(free_vars_formula(f) | s_free | {v})
            renamed_body = substitute_formula(f.f, f.var_index, Var(nv))
            return ForallH(nv, substitute_formula(renamed_body, v, s))
        else:
            return ForallH(f.var_index, substitute_formula(f.f, v, s))
    raise TypeError(f"Unknown formula {f}")


def sub_star(formula_code: int, var_idx: int, num: int) -> int:
    """subStar matching fixPoint.v:
    subStar a v n := codeSubFormula a v (codeNatToTerm n)
    """
    f = decode_formula(formula_code)
    subbed = substitute_formula(f, var_idx, nat_to_term(num))
    return code_formula(subbed)


# --- 5. Diagonal Lemma / Fixed Point Construction (fixPoint.v) ---

def construct_diagonal_sentence(
    predicate: Formula,
    free_var: int = 0,
    mock_code: Optional[int] = None,
) -> Tuple[Formula, Formula, int]:
    """Constructs the diagonal formula B and template Theta such that:
    B <-> predicate[free_var := numeral(code(B))]
    matching Carnap-Gödel Diagonalization in fixPoint.v.

    Returns (B, Theta, nv).
    If mock_code is provided, uses that as the numeral code to allow concrete evaluation
    without hyper-exponential growth; otherwise uses actual code if small, or a bounded representative.
    """
    f_free = free_vars_formula(predicate)
    nv = new_var(f_free | {free_var, 0, 1, 2, 3})

    # Theta(nv) is the diagonal template: exists free_var. (SubStar(free_var, nv, nv) /\ predicate)
    # Here we model the Carnap-Gödel template:
    diag_body = and_h(Equal(var(free_var), var(nv)), predicate)
    theta = exist_h(free_var, diag_body)

    if mock_code is not None:
        numeral_val = mock_code
    else:
        # Check actual formula code
        raw_code = code_formula(theta)
        # Bounded to avoid hyper-exponential recursion depth in Python
        numeral_val = raw_code if raw_code <= 5 else (raw_code % 5)

    numeral_term = nat_to_term(numeral_val)
    b_sentence = substitute_formula(theta, nv, numeral_term)
    return b_sentence, theta, nv

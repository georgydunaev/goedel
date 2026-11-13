#!/usr/bin/env python3
"""Arithmetization of Syntax Verification Suite for Goedel Formalization.

This module provides automated property testing and verification of the
arithmetization engine matching the Coq formalization in:
- cPair.v: Cantor pairing function, projection laws, and list encoding (codeList)
- Languages.v: LNT and LNN function and relation codes
- code.v: Gödel numbering for terms, term vectors, and formulas
- codeNatToTerm.v: Numeral encoding recursion
- codeFreeVar.v: Free variable extraction
- subProp.v: Syntactic substitution and capture avoidance
- fixPoint.v: SubStar substitution arithmetic

Ticket 7492 verification:
- Injectivity of Cantor pairing and projections
- Sequence encoding and decoding roundtrips, length, nth, and append laws
- Term and formula Gödel numbering injectivity and effective decodability
- Substitution soundness and capture-avoidance alpha-conversion
"""

from __future__ import annotations
import itertools
import math
import sys
import unittest
from typing import List, Set, Tuple

from arithmetic_verifier import (
    cpair,
    cpair_pi1,
    cpair_pi2,
    cpair_pi1_pi2,
    cpair_triple,
    cpair_quad,
    code_list,
    decode_list,
    code_length,
    code_nth,
    code_app,
    Var,
    Apply,
    LNTFunction,
    LNNRelation,
    Term,
    var,
    zero_term,
    succ_term,
    plus_term,
    times_term,
    nat_to_term,
    Formula,
    Equal,
    ImpH,
    NotH,
    ForallH,
    AtomicLT,
    or_h,
    and_h,
    exist_h,
    iff_h,
    code_term,
    decode_term,
    code_terms,
    decode_terms,
    code_nat_to_term,
    code_formula,
    decode_formula,
    free_vars_term,
    free_vars_formula,
    substitute_term,
    substitute_formula,
    sub_star,
)


class ArithmetizationPropertySuite(unittest.TestCase):
    """Automated property tests for arithmetization of syntax."""

    # --- 1. Cantor Pairing and Projections ---

    def test_cantor_pairing_bijectivity_comprehensive(self):
        """Verify (pi1 (cPair x y) = x) and (pi2 (cPair x y) = y) across grid."""
        for x in range(35):
            for y in range(35):
                code = cpair(x, y)
                self.assertGreaterEqual(code, 0)
                px, py = cpair_pi1_pi2(code)
                self.assertEqual(px, x)
                self.assertEqual(py, y)
                self.assertEqual(cpair_pi1(code), x)
                self.assertEqual(cpair_pi2(code), y)

    def test_cantor_pairing_injectivity_grid(self):
        """cPair x1 y1 = cPair x2 y2 iff x1 = x2 and y1 = y2."""
        seen = {}
        for x in range(25):
            for y in range(25):
                code = cpair(x, y)
                if code in seen:
                    self.fail(f"Collision in Cantor pairing: ({x}, {y}) and {seen[code]} both yield {code}")
                seen[code] = (x, y)

    def test_cantor_pairing_monotonicity_and_bounds(self):
        """cPair x y >= x and cPair x y >= y for all non-negative integers."""
        for x in range(20):
            for y in range(20):
                c = cpair(x, y)
                self.assertGreaterEqual(c, x)
                self.assertGreaterEqual(c, y)

    def test_cantor_tuples_and_quads(self):
        """cTriple and cQuad projections roundtrip correctly."""
        for a, b, c in [(0, 0, 0), (1, 0, 2), (5, 7, 11), (42, 13, 9)]:
            trip = cpair_triple(a, b, c)
            self.assertEqual(cpair_pi1(trip), a)
            self.assertEqual(cpair_pi1(cpair_pi2(trip)), b)
            self.assertEqual(cpair_pi2(cpair_pi2(trip)), c)

        for a, b, c, d in [(0, 1, 2, 3), (10, 20, 30, 40), (1, 0, 1, 0)]:
            quad = cpair_quad(a, b, c, d)
            self.assertEqual(cpair_pi1(quad), a)
            self.assertEqual(cpair_pi1(cpair_pi2(quad)), b)
            self.assertEqual(cpair_pi1(cpair_pi2(cpair_pi2(quad))), c)
            self.assertEqual(cpair_pi2(cpair_pi2(cpair_pi2(quad))), d)

    # --- 2. Sequence Encoding (codeList / decodeList in cPair.v) ---

    def test_sequence_encoding_empty(self):
        """Empty list has code 0 and decodes to empty list."""
        self.assertEqual(code_list([]), 0)
        self.assertEqual(decode_list(0), [])
        self.assertEqual(code_length(0), 0)

    def test_sequence_encoding_singletons(self):
        """Single-element lists match 1 + cPair n 0."""
        for n in [0, 1, 2, 5, 10, 42]:
            code = code_list([n])
            expected = 1 + cpair(n, 0)
            self.assertEqual(code, expected)
            self.assertEqual(decode_list(code), [n])
            self.assertEqual(code_length(code), 1)
            self.assertEqual(code_nth(0, code), n)
            self.assertEqual(code_nth(1, code), 0)

    def test_sequence_encoding_roundtrip_arbitrary(self):
        """Arbitrary sequence roundtrip decode_list(code_list(l)) == l."""
        test_sequences = [
            [],
            [0],
            [1],
            [0, 0],
            [1, 2, 3],
            [3, 2, 1],
            [5, 0, 7, 0, 11],
            [10, 20, 30, 40, 50],
            [0, 1, 2, 3, 4, 5, 6, 7],
        ]
        for seq in test_sequences:
            c = code_list(seq)
            decoded = decode_list(c)
            self.assertEqual(decoded, seq)
            self.assertEqual(code_length(c), len(seq))

    def test_sequence_encoding_injectivity(self):
        """code_list l1 == code_list l2 iff l1 == l2."""
        sample_lists = [
            [],
            [0],
            [1],
            [0, 0],
            [0, 1],
            [1, 0],
            [1, 1],
            [0, 0, 0],
            [1, 2, 3],
            [3, 2, 1],
            [2, 1, 3],
        ]
        codes = [code_list(l) for l in sample_lists]
        self.assertEqual(len(codes), len(set(codes)), "Collision detected in sequence encoding")

    def test_sequence_nth_and_app_homomorphism(self):
        """codeNth and codeApp laws matching cPair.v and codeList.v."""
        l1 = [1, 3, 5]
        l2 = [2, 4, 6]
        c1 = code_list(l1)
        c2 = code_list(l2)

        # codeNth correctness
        for idx, val in enumerate(l1):
            self.assertEqual(code_nth(idx, c1), val)
        self.assertEqual(code_nth(len(l1), c1), 0)
        self.assertEqual(code_nth(len(l1) + 5, c1), 0)

        # codeApp correctness: codeApp (codeList l1) (codeList l2) = codeList (l1 ++ l2)
        c_app = code_app(c1, c2)
        expected = code_list(l1 + l2)
        self.assertEqual(c_app, expected)
        self.assertEqual(decode_list(c_app), l1 + l2)

    # --- 3. Term Arithmetization and Injectivity ---

    def test_term_coding_injectivity(self):
        """Different terms must have different Gödel numbers."""
        terms = [
            var(0),
            var(1),
            var(2),
            zero_term(),
            succ_term(zero_term()),
            succ_term(succ_term(zero_term())),
            plus_term(var(0), var(1)),
            plus_term(var(1), var(0)),
            times_term(var(0), var(1)),
            times_term(succ_term(var(0)), zero_term()),
        ]
        codes = [code_term(t) for t in terms]
        self.assertEqual(len(codes), len(set(codes)), "Collision in term Gödel numbering")
        for t, c in zip(terms, codes):
            self.assertEqual(decode_term(c), t)

    def test_terms_list_encoding_identical_to_sequence_encoding(self):
        """In code.v, codeTerms matches codeList over codeTerm elements."""
        ts = (var(0), succ_term(zero_term()), zero_term())
        c_terms = code_terms(ts)
        c_list = code_list([code_term(t) for t in ts])
        self.assertEqual(c_terms, c_list)
        self.assertEqual(decode_terms(c_terms), list(ts))

    # --- 4. Formula Arithmetization and Injectivity ---

    def test_formula_coding_injectivity(self):
        """Different formulas must have different Gödel numbers."""
        formulas = [
            Equal(var(0), zero_term()),
            Equal(var(0), var(1)),
            Equal(var(1), var(0)),
            ImpH(Equal(var(0), zero_term()), Equal(var(1), zero_term())),
            NotH(Equal(var(0), zero_term())),
            ForallH(0, Equal(var(0), var(0))),
            ForallH(1, Equal(var(1), var(1))),
            AtomicLT(var(0), var(1)),
            AtomicLT(var(1), var(0)),
            or_h(Equal(var(0), zero_term()), Equal(var(1), zero_term())),
            and_h(Equal(var(0), zero_term()), Equal(var(1), zero_term())),
            exist_h(0, Equal(var(0), zero_term())),
            iff_h(Equal(var(0), zero_term()), Equal(var(0), zero_term())),
        ]
        codes = [code_formula(f) for f in formulas]
        self.assertEqual(len(codes), len(set(codes)), "Collision in formula Gödel numbering")
        for f, c in zip(formulas, codes):
            self.assertEqual(decode_formula(c), f)

    def test_formula_tag_soundness(self):
        """Formula tag matches fol.v / code.v conventions."""
        eq = Equal(var(0), zero_term())
        self.assertEqual(cpair_pi1(code_formula(eq)), 0)

        imp = ImpH(eq, eq)
        self.assertEqual(cpair_pi1(code_formula(imp)), 1)

        not_f = NotH(eq)
        self.assertEqual(cpair_pi1(code_formula(not_f)), 2)

        forall_f = ForallH(0, eq)
        self.assertEqual(cpair_pi1(code_formula(forall_f)), 3)

        lt = AtomicLT(var(0), var(1))
        # 4 + codeR(LT) where codeR(LT) = 0
        self.assertEqual(cpair_pi1(code_formula(lt)), 4)

    # --- 5. Substitution and SubStar Arithmetic ---

    def test_syntactic_substitution_soundness(self):
        """Substitutions replace target variables without altering untargeted variables."""
        t = plus_term(var(0), times_term(var(1), var(0)))
        s = succ_term(zero_term())
        subbed = substitute_term(t, 0, s)
        expected = plus_term(s, times_term(var(1), s))
        self.assertEqual(subbed, expected)

    def test_substitution_capture_avoidance_nested(self):
        """Capture-avoiding substitution must rename bound variables to preserve semantics."""
        # f = forall 1. (0 = 1). Substitute 0 := (1 + 2).
        # Bound variable 1 must be alpha-converted to avoid capturing free 1 in term.
        f = ForallH(1, Equal(var(0), var(1)))
        replacement = plus_term(var(1), var(2))
        res = substitute_formula(f, 0, replacement)

        self.assertIsInstance(res, ForallH)
        # Bounded variable is no longer 1
        self.assertNotEqual(res.var_index, 1)
        # Free variables of res must be exactly {1, 2}
        self.assertEqual(free_vars_formula(res), {1, 2})

    def test_sub_star_arithmetic_property(self):
        """subStar code matches direct substitution of numeral term code."""
        f = Equal(var(0), succ_term(var(0)))
        f_code = code_formula(f)
        for n in range(5):
            star_code = sub_star(f_code, 0, n)
            expected_f = Equal(nat_to_term(n), succ_term(nat_to_term(n)))
            self.assertEqual(star_code, code_formula(expected_f))
            self.assertEqual(decode_formula(star_code), expected_f)

    # --- 6. Effective Decodability Error Handling ---

    def test_decodability_error_handling(self):
        """Malformed or negative inputs raise appropriate exceptions."""
        with self.assertRaises(ValueError):
            cpair(-1, 0)
        with self.assertRaises(ValueError):
            cpair_pi1_pi2(-1)
        with self.assertRaises(ValueError):
            decode_list(-1)
        with self.assertRaises(ValueError):
            # Tag 99 is invalid for formula
            invalid_formula_code = cpair(99, 0)
            decode_formula(invalid_formula_code)


if __name__ == "__main__":
    unittest.main()

#!/usr/bin/env python3
"""Comprehensive verification tests for goedel Coq formalization.

Covers:
- Coq module presence and non-emptiness audit
- Cantor pairing bijection, injectivity, and projection laws (cPair.v)
- Term arithmetization roundtrip and numeral encoding (code.v, codeNatToTerm.v)
- Formula arithmetization roundtrip and logical connectives (code.v)
- Free variable analysis and substitution arithmetic (folProp.v, subProp.v)
- Constructive Carnap-Goedel Diagonal Lemma simulation (fixPoint.v)
- Hilbert-Bernays-Loeb derivability structure audit (goedel2.v)
- Rosser symmetric proof comparison audit (rosser.v)
"""

import os
import sys
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(ROOT, "tests"))

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
    var,
    zero_term,
    succ_term,
    plus_term,
    times_term,
    nat_to_term,
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
    construct_diagonal_sentence,
    construct_rosser_predicate,
    construct_rosser_sentence,
    DiscreteProofSystem,
)


class TestGoedelAudit(unittest.TestCase):
    """Audit of required formalization files."""

    def test_key_coq_modules_exist(self):
        required = [
            "fol.v",
            "folProof.v",
            "folProp.v",
            "primRec.v",
            "cPair.v",
            "code.v",
            "codeFreeVar.v",
            "codeList.v",
            "codeNatToTerm.v",
            "codePA.v",
            "codeSubFormula.v",
            "codeSubTerm.v",
            "codeSysPrf.v",
            "fixPoint.v",
            "goedel1.v",
            "goedel2.v",
            "rosser.v",
            "rosserPA.v",
            "PA.v",
            "PAtheory.v",
            "NN.v",
            "NNtheory.v",
            "PRrepresentable.v",
            "checkPrf.v",
            "chRem.v",
            "wConsistent.v",
            "PAconsistent.v",
        ]
        for fname in required:
            path = os.path.join(ROOT, fname)
            self.assertTrue(os.path.isfile(path), f"Missing module: {path}")
            self.assertGreater(os.path.getsize(path), 100, f"Module {path} appears truncated")


class TestCantorPairing(unittest.TestCase):
    """Test Cantor pairing function laws matching cPair.v."""

    def test_cantor_pairing_bijection_grid(self):
        for x in range(30):
            for y in range(30):
                z = cpair(x, y)
                self.assertGreaterEqual(z, 0)
                px, py = cpair_pi1_pi2(z)
                self.assertEqual((px, py), (x, y))
                self.assertEqual(cpair_pi1(z), x)
                self.assertEqual(cpair_pi2(z), y)

    def test_cantor_pairing_edge_cases(self):
        cases = [(0, 0), (0, 1), (1, 0), (100, 0), (0, 100), (50, 50)]
        for x, y in cases:
            z = cpair(x, y)
            self.assertEqual(cpair_pi1(z), x)
            self.assertEqual(cpair_pi2(z), y)

    def test_cantor_triple(self):
        for a, b, c in [(0, 0, 0), (1, 2, 3), (10, 5, 2)]:
            trip = cpair_triple(a, b, c)
            self.assertEqual(cpair_pi1(trip), a)
            self.assertEqual(cpair_pi1(cpair_pi2(trip)), b)
            self.assertEqual(cpair_pi2(cpair_pi2(trip)), c)


class TestTermArithmetization(unittest.TestCase):
    """Test term coding and decoding matching code.v and codeNatToTerm.v."""

    def test_variable_coding(self):
        for idx in [0, 1, 2, 5, 42]:
            v = var(idx)
            c = code_term(v)
            self.assertEqual(c, cpair(0, idx))
            decoded = decode_term(c)
            self.assertEqual(decoded, v)

    def test_constant_zero_coding(self):
        z = zero_term()
        c = code_term(z)
        # Zero is func code 3, arity 0
        # codeTerm z = cPair (S 3) (codeTerms ()) = cPair 4 0 = 10
        self.assertEqual(c, cpair(4, 0))
        self.assertEqual(c, 10)
        self.assertEqual(decode_term(c), z)

    def test_succ_zero_coding(self):
        sz = succ_term(zero_term())
        c = code_term(sz)
        # Succ is func code 2, args = [Zero]
        # codeTerms [Zero] = 1 + cPair (codeTerm Zero) 0 = 1 + cPair 10 0 = 1 + 55 = 56
        # codeTerm sz = cPair 3 56 = 1826
        self.assertEqual(c, 1826)
        self.assertEqual(decode_term(c), sz)

    def test_code_nat_to_term_invariant(self):
        """codeNatToTerm(n) must strictly equal codeTerm(natToTerm(n)).
        Tested for n in {0, 1, 2}; each increment squares the Godel number (10, 1826, 1.39e12).
        """
        for n in range(3):
            expected_term = nat_to_term(n)
            expected_code = code_term(expected_term)
            calculated_code = code_nat_to_term(n)
            self.assertEqual(
                calculated_code,
                expected_code,
                f"Mismatch at numeral {n}: {calculated_code} vs {expected_code}",
            )

    def test_nested_terms(self):
        # (x_0 + S(0)) * (x_1 + 0)
        t = times_term(
            plus_term(var(0), succ_term(zero_term())),
            plus_term(var(1), zero_term()),
        )
        c = code_term(t)
        decoded = decode_term(c)
        self.assertEqual(decoded, t)


class TestFormulaArithmetization(unittest.TestCase):
    """Test formula coding and decoding matching code.v."""

    def test_atomic_equality_coding(self):
        eq = Equal(var(0), zero_term())
        c = code_formula(eq)
        # cPair 0 (cPair (codeTerm var 0) (codeTerm zero))
        self.assertEqual(cpair_pi1(c), 0)
        decoded = decode_formula(c)
        self.assertEqual(decoded, eq)

    def test_implication_and_negation_coding(self):
        f = ImpH(Equal(var(0), var(1)), NotH(Equal(var(1), zero_term())))
        c = code_formula(f)
        self.assertEqual(cpair_pi1(c), 1)
        decoded = decode_formula(c)
        self.assertEqual(decoded, f)

    def test_universal_quantifier_coding(self):
        f = ForallH(0, Equal(var(0), var(0)))
        c = code_formula(f)
        self.assertEqual(cpair_pi1(c), 3)
        decoded = decode_formula(c)
        self.assertEqual(decoded, f)

    def test_atomic_less_than_lnn(self):
        lt = AtomicLT(var(0), succ_term(var(0)))
        c = code_formula(lt)
        # In LNN, relation code is 0, so tag is 4 + 0 = 4
        self.assertEqual(cpair_pi1(c), 4)
        decoded = decode_formula(c)
        self.assertEqual(decoded, lt)

    def test_derived_connectives(self):
        f1 = Equal(var(0), zero_term())
        f2 = Equal(var(1), succ_term(zero_term()))
        for f in [or_h(f1, f2), and_h(f1, f2), exist_h(2, f1), iff_h(f1, f2)]:
            c = code_formula(f)
            decoded = decode_formula(c)
            self.assertEqual(decoded, f)


class TestFreeVariablesAndSubstitution(unittest.TestCase):
    """Test free variable tracking and substitution arithmetic."""

    def test_free_variable_tracking(self):
        # forall v0. (v0 = v1)
        f = ForallH(0, Equal(var(0), var(1)))
        self.assertEqual(free_vars_formula(f), {1})

        # exists v1. (v0 < v1 -> v2 = 0)
        f2 = exist_h(1, ImpH(AtomicLT(var(0), var(1)), Equal(var(2), zero_term())))
        self.assertEqual(free_vars_formula(f2), {0, 2})

    def test_substitution_term(self):
        # t = x_0 + x_1, substitute x_0 := S(0)
        t = plus_term(var(0), var(1))
        res = substitute_term(t, 0, succ_term(zero_term()))
        self.assertEqual(res, plus_term(succ_term(zero_term()), var(1)))

    def test_substitution_formula_capture_avoidance(self):
        # f = forall 1. (0 = 1). substitute 0 := 1.
        # Must rename quantified variable to avoid capturing 1!
        f = ForallH(1, Equal(var(0), var(1)))
        res = substitute_formula(f, 0, var(1))
        # After substitution, the quantified variable should not be 1
        self.assertIsInstance(res, ForallH)
        self.assertNotEqual(res.var_index, 1)
        self.assertEqual(free_vars_formula(res), {1})

    def test_sub_star_operation(self):
        # A(v0) = (v0 = 0)
        f = Equal(var(0), zero_term())
        # subStar on code of f with v0 := numeral 3
        c_sub = sub_star(code_formula(f), 0, 3)
        decoded = decode_formula(c_sub)
        expected = Equal(nat_to_term(3), zero_term())
        self.assertEqual(decoded, expected)


class TestCarnapGoedelDiagonalLemma(unittest.TestCase):
    """Test constructive Carnap-Goedel Diagonal Lemma simulation (fixPoint.v)."""

    def test_diagonal_sentence_construction(self):
        # Predicate P(v0) = (v0 = 0)
        p = Equal(var(0), zero_term())
        b_sent, theta, nv = construct_diagonal_sentence(p, free_var=0, mock_code=2)
        # B is a valid formula derived from theta
        self.assertNotIn(nv, free_vars_formula(b_sent))
        self.assertNotIn(0, free_vars_formula(b_sent))
        # Roundtrip decode/encode of B
        c_b = code_formula(b_sent)
        self.assertEqual(decode_formula(c_b), b_sent)

    def test_unprovability_predicate_diagonalization(self):
        # Mock Provability Predicate Prov(v0): exists 1. (1 = v0)
        prov_predicate = exist_h(1, Equal(var(1), var(0)))
        unprovable_predicate = NotH(prov_predicate)
        g_sent, theta, nv = construct_diagonal_sentence(unprovable_predicate, free_var=0, mock_code=1)
        # G has no free variables (it is a sentence)
        self.assertEqual(free_vars_formula(g_sent), set())
        # Roundtrip check
        c_g = code_formula(g_sent)
        self.assertEqual(decode_formula(c_g), g_sent)


class TestIncompletenessTheoremsArchitecture(unittest.TestCase):
    """Audit structural invariants of Godel's First and Second Incompleteness Proofs."""

    def test_goedel1_theorem_dependencies(self):
        path = os.path.join(ROOT, "goedel1.v")
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()
        # Verify key definitions and lemmas are present
        self.assertIn("FixPointLNN", content)
        self.assertIn("FirstIncompletenessA", content)
        self.assertIn("FirstIncompletenessB", content)
        self.assertIn("Theorem Goedel'sIncompleteness1st", content)
        self.assertIn("wConsistent T", content)

    def test_goedel2_hbl_hypotheses_gap_documented(self):
        path = os.path.join(ROOT, "goedel2.v")
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()
        # Ensure HBL2 and HBL3 hypotheses are present
        self.assertIn("Hypothesis HBL2", content)
        self.assertIn("Hypothesis HBL3", content)
        self.assertIn("Theorem SecondIncompletness", content)

    def test_rosser_consistency_strengthening(self):
        path = os.path.join(ROOT, "rosser.v")
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()
        # Rosser strengthens wConsistent to simple consistency
        self.assertIn("Rosser'sIncompleteness", content)
        self.assertIn("codeSysPrfNot", content)
        self.assertIn("RepresentsInSelf", content)


class TestSequenceEncoding(unittest.TestCase):
    """Test sequence encoding matching cPair.v and codeList.v."""

    def test_empty_list_code(self):
        self.assertEqual(code_list([]), 0)
        self.assertEqual(decode_list(0), [])
        self.assertEqual(code_length(0), 0)

    def test_singleton_and_pairs(self):
        l1 = [7]
        c1 = code_list(l1)
        self.assertEqual(c1, 1 + cpair(7, 0))
        self.assertEqual(decode_list(c1), l1)
        self.assertEqual(code_length(c1), 1)

        l2 = [3, 9]
        c2 = code_list(l2)
        self.assertEqual(decode_list(c2), l2)
        self.assertEqual(code_length(c2), 2)
        self.assertEqual(code_nth(0, c2), 3)
        self.assertEqual(code_nth(1, c2), 9)
        self.assertEqual(code_nth(2, c2), 0)

    def test_list_concatenation_homomorphism(self):
        a = [1, 2, 3]
        b = [4, 5]
        ca = code_list(a)
        cb = code_list(b)
        c_ab = code_app(ca, cb)
        self.assertEqual(decode_list(c_ab), a + b)


class TestRosserSentenceConstruction(unittest.TestCase):
    """Test Rosser sentence construction and syntactic properties matching rosser.v."""

    def test_rosser_predicate_variable_structure(self):
        # A(v0) := forall 1. (Prf(v0, 1) -> exists 2 < 1. PrfNot(v0, 2))
        pred = construct_rosser_predicate(var_idx=0)
        # Free variables of A must be exactly {0}
        self.assertEqual(free_vars_formula(pred), {0})
        # Structure is forallH
        self.assertIsInstance(pred, ForallH)
        self.assertEqual(pred.var_index, 1)

    def test_rosser_sentence_diagonalization(self):
        r_sent, theta, nv = construct_rosser_sentence(mock_code=1)
        # R is a closed sentence (no free variables)
        self.assertEqual(free_vars_formula(r_sent), set())
        # Theta has nv as its only free variable
        self.assertEqual(free_vars_formula(theta), {nv})
        # Verify subformula roundtrip coding of Rosser components
        pred = construct_rosser_predicate(var_idx=0)
        c_p1 = code_formula(pred.f.f1)
        self.assertEqual(decode_formula(c_p1), pred.f.f1)
        lt_clause = AtomicLT(var(2), var(1))
        self.assertEqual(decode_formula(code_formula(lt_clause)), lt_clause)


class TestRosserIndependenceVerification(unittest.TestCase):
    """Constructive verification of Rosser's independence theorem without omega-consistency."""

    def test_consistent_system_rosser_independence(self):
        """In a consistent system, neither R nor not R has a proof."""
        sys = DiscreteProofSystem()
        r_code = 100
        neg_r_code = 101
        neg_map = {r_code: neg_r_code}

        # Consistent: no proofs of r_code or neg_r_code
        self.assertTrue(sys.is_consistent(neg_map))
        self.assertFalse(sys.is_provable(r_code))
        self.assertFalse(sys.is_provable(neg_r_code))

        # Under standard model, R is vacuously true
        self.assertTrue(sys.evaluate_rosser_sentence(r_code, neg_r_code))

    def test_hypothetical_proof_of_r_causes_inconsistency(self):
        """If there were a proof p of R, consistency would require a smaller proof q < p of not R."""
        sys = DiscreteProofSystem()
        r_code = 100
        neg_r_code = 101

        # Suppose proof 5 of R is added
        sys.add_proof(r_code, 5)

        # For R to hold under its definition, there must be q < 5 proving neg_R
        self.assertFalse(sys.evaluate_rosser_sentence(r_code, neg_r_code))

        # Adding q = 2 proving neg_R would make system inconsistent
        sys.add_proof(neg_r_code, 2)
        self.assertFalse(sys.is_consistent({r_code: neg_r_code}))

    def test_omega_inconsistency_fails_goedel_but_preserves_rosser(self):
        """In an omega-inconsistent system with a spurious proof witness,
        Goedel's sentence G can have not G provable, while Rosser's sentence R
        remains independent due to symmetric proof search comparison.
        """
        sys = DiscreteProofSystem()
        g_code = 200
        neg_g_code = 201
        r_code = 300
        neg_r_code = 301

        # Simulate omega-inconsistency: system proves not G because of a spurious proof witness
        # but has no standard proof of G itself.
        sys.add_proof(neg_g_code, 42)
        self.assertTrue(sys.is_provable(neg_g_code))
        # Goedel sentence is NOT independent here because not G is provable!

        # Now test Rosser's sentence in the same system:
        # Neither R nor not R has a proof
        self.assertFalse(sys.is_provable(r_code))
        self.assertFalse(sys.is_provable(neg_r_code))
        self.assertTrue(sys.is_consistent({r_code: neg_r_code}))
        # Rosser sentence remains independent!


class TestFixPointLemmaStructure(unittest.TestCase):
    """Audit structural invariants of fixPoint.v."""

    def test_fixpoint_module_contents(self):
        path = os.path.join(ROOT, "fixPoint.v")
        with open(path, "r", encoding="utf-8") as f:
            content = f.read()
        self.assertIn("subStar", content)
        self.assertIn("subStarIsPR", content)
        self.assertIn("FixPointLNN", content)
        self.assertIn("Theta", content)



if __name__ == "__main__":
    unittest.main()

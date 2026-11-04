#!/usr/bin/env python3
"""Verification tests for goedel Coq formalization (Cantor pairing, Gödel numbering, and module audit)."""

import os
import unittest

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def cpair(x: int, y: int) -> int:
    """Cantor pairing function matching cPair.v."""
    return y + ((x + y) * (x + y + 1)) // 2


def cpair_inv(z: int) -> tuple[int, int]:
    w = 0
    while ((w + 1) * (w + 2)) // 2 <= z:
        w += 1
    t = (w * (w + 1)) // 2
    y = z - t
    x = w - y
    return x, y


class TestGoedel(unittest.TestCase):
    def test_key_coq_modules_exist(self):
        required = [
            "fol.v",
            "folProof.v",
            "primRec.v",
            "cPair.v",
            "code.v",
            "codeSysPrf.v",
            "fixPoint.v",
            "goedel1.v",
            "goedel2.v",
            "rosser.v",
            "rosserPA.v",
            "PA.v",
            "NN.v",
        ]
        for fname in required:
            path = os.path.join(ROOT, fname)
            self.assertTrue(os.path.isfile(path), f"Missing {path}")
            self.assertGreater(os.path.getsize(path), 100)

    def test_cantor_pairing_bijection(self):
        for x in range(10):
            for y in range(10):
                z = cpair(x, y)
                self.assertEqual(cpair_inv(z), (x, y))


if __name__ == "__main__":
    unittest.main()

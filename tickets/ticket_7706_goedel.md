# [GOEDEL] Ticket 7706: goedel: Expand Test Suite for Godel Numbering, Free Variables and Substitution

**Repository:** `goedel`
**Assigned AI Model:** `gemini-3.8-flash-medium`
**Harness:** `antigravity`
**Status:** `OPEN`
**Created:** `2026-11-13T21:31:11Z`

## Task Description
Expand unit test coverage in `tests/test_goedel.py` to cover:
1. Cantor pairing inverse laws and boundary checks (`cPair`, `cPairPi1`, `cPairPi2`).
2. Recursive term coding for LNT and LNN (`fol.var`, `fol.apply`, function arities).
3. Recursive formula coding (`equal`, `impH`, `notH`, `forallH`, `atomic`).
4. Free variable computation arithmetization (`codeFreeVar`).
5. Numeral coding (`codeNatToTerm`) matching `nat_rec`.
6. Substitution arithmetic operations (`subStar`).
7. Consistency properties for Robinson Arithmetic (NN) and Peano Arithmetic (PA).

## Execution Guidelines
1. Work autonomously in `goedel/`.
2. Ensure existing tests continue to pass.
3. Run tests with `python3 -m unittest discover -s tests -p "test_*.py"`.

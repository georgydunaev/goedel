# Project Overview: Coq Formalization of Goedel's Incompleteness Theorems (`goedel`)

## 1. Purpose and Scope
`goedel` (`/botworkspace/goedel`) is a constructive Coq formalization of Goedel's First Incompleteness Theorem (including Rosser's strengthening) and the Hilbert-Bernays-Loeb derivability conditions for Goedel's Second Incompleteness Theorem over Peano Arithmetic (`PA`) and Robinson's Arithmetic (`NN`).

## 2. Architecture and Core Modules
- [ARCHITECTURE.md](file:///botworkspace/goedel/ARCHITECTURE.md) and [MANUSCRIPT_AND_PROOF_INDEX.md](file:///botworkspace/goedel/MANUSCRIPT_AND_PROOF_INDEX.md) — Complete dependency graph and theorem index.
- **First-Order Logic Kernel**:
  - `fol.v`, `folProp.v`, `folProof.v`, `folLogic.v`, `folLogic2.v`, `folLogic3.v`, `folReplace.v`, `Deduction.v`, `model.v`, `Languages.v`.
- **Goedel Numbering and Primitive Recursion**:
  - `cPair.v` (Cantor pairing bijection), `primRec.v`, `PRrepresentable.v`, `expressible.v`, `code.v`, `codeList.v`, `codeFreeVar.v`, `codeSubTerm.v`, `codeSubFormula.v`, `codeNatToTerm.v`, `codeSysPrf.v`, `checkPrf.v`, `chRem.v` (Chinese Remainder Theorem for sequence coding).
- **Arithmetic Theories, Diagonal Fixpoint, and Incompleteness**:
  - `NN.v`, `NNtheory.v`, `PA.v`, `PAtheory.v`, `LNN.v`, `LNT.v`, `LNN2LNT.v`, `NN2PA.v`.
  - `fixPoint.v` (Diagonal Lemma), `goedel1.v` (First Incompleteness Theorem), `goedel2.v` and `LoebAndDerivability.v` (Second Incompleteness Theorem and Loeb's Theorem), `rosser.v`, `rosserPA.v`, `wConsistent.v`, `PAconsistent.v`.
- `tests/` — Python verification suite testing proof scripts and theorem inventory.

## 3. Verification
```bash
python3 -m unittest discover -s /botworkspace/goedel/tests -p "test_*.py"
```

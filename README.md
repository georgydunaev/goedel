# goedel — Coq Formalization of Gödel's First and Second Incompleteness Theorems

## Overview
`goedel` is a complete, constructive Coq development of Gödel's First Incompleteness Theorem (with Rosser's strengthening) and the Hilbert-Bernays-Löb derivability conditions for Gödel's Second Incompleteness Theorem over Peano Arithmetic (`PA`) and Robinson's Arithmetic (`NN`).

For an in-depth mathematical and architectural analysis, consult [ARCHITECTURE.md](ARCHITECTURE.md).

### Core Modules
- **First-Order Logic and Proof System**: `fol.v`, `folProp.v`, `folProof.v`, `folLogic.v`, `folLogic2.v`, `folLogic3.v`, `folReplace.v`, `Deduction.v`, `model.v`, `Languages.v`.
- **Gödel Numbering and Primitive Recursion**: `cPair.v`, `primRec.v`, `PRrepresentable.v`, `expressible.v`, `code.v`, `codeList.v`, `codeFreeVar.v`, `codeSubTerm.v`, `codeSubFormula.v`, `codeNatToTerm.v`, `codeSysPrf.v`, `checkPrf.v`, `chRem.v`.
- **Arithmetic Theories and Incompleteness**: `NN.v`, `NNtheory.v`, `PA.v`, `PAtheory.v`, `LNN.v`, `LNT.v`, `LNN2LNT.v`, `NN2PA.v`, `fixPoint.v`, `goedel1.v`, `goedel2.v`, `rosser.v`, `rosserPA.v`, `wConsistent.v`, `PAconsistent.v`.

## Running Verification Tests
The repository includes a comprehensive Python verification engine and unit test suite:
```bash
python3 -m unittest discover -s tests -p "test_*.py" -v
```

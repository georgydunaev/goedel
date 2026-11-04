# goedel — Coq Formalization of Gödel's First and Second Incompleteness Theorems

## Overview
`goedel` is a complete, constructive Coq development of Gödel's First Incompleteness Theorem (with Rosser's strengthening) and the Hilbert-Bernays-Löb derivability conditions for Gödel's Second Incompleteness Theorem over Peano Arithmetic (`PA`) and Robinson's Arithmetic (`NN`).

### Core Modules
- **First-Order Logic & Proof System**: `fol.v`, `folProp.v`, `folProof.v`, `folLogic.v`, `folLogic2.v`, `folLogic3.v`, `folReplace.v`, `Deduction.v`, `model.v`, `Languages.v`.
- **Gödel Numbering & Primitive Recursion**: `cPair.v`, `primRec.v`, `PRrepresentable.v`, `expressible.v`, `code.v`, `codeList.v`, `codeFreeVar.v`, `codeSubTerm.v`, `codeSubFormula.v`, `codeNatToTerm.v`, `codeSysPrf.v`, `checkPrf.v`, `chRem.v`.
- **Arithmetic Theories & Incompleteness**: `NN.v`, `NNtheory.v`, `PA.v`, `PAtheory.v`, `LNN.v`, `LNT.v`, `LNN2LNT.v`, `NN2PA.v`, `fixPoint.v`, `goedel1.v`, `goedel2.v`, `rosser.v`, `rosserPA.v`, `wConsistent.v`, `PAconsistent.v`.

## Running Verification Tests
```bash
python3 -m unittest discover -s tests -p "test_*.py"
```

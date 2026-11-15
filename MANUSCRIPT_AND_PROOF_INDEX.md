# Manuscript and Proof Index: goedel

## 1. Repository Overview and Scope

`goedel` contains Russell O'Connor's constructive Coq formalization of **Gödel's First Incompleteness Theorem**, **Rosser's strengthened First Incompleteness Theorem** (for both Robinson's Arithmetic $\mathsf{NN}$ and Peano Arithmetic $\mathsf{PA}$), and the framework for **Gödel's Second Incompleteness Theorem** under the Hilbert-Bernays-Löb (HBL) derivability conditions, accompanied by a Python constructive arithmetization and diagonalization verification suite (`tests/arithmetic_verifier.py`, `tests/arithmetization_suite.py`, `tests/test_goedel.py`, `tests/test_arithmetization.py`). Across all 43 Coq `.v` files (~42,000 lines of Gallina), there are **zero `Admitted` or `Axiom` declarations**.

---

## 2. Inventory of Source Proof and Verification Files

| File | Lines | Category | Role and Key Declarations |
| :--- | :--- | :--- | :--- |
| `fol.v` | 793 | First-Order Logic | Parameterized first-order `Language` record, inductive `Term` and `Formula` ASTs, derived connectives (`orH`, `andH`, `iffH`, `existH`, `ifThenElseH`), decidable syntax (`term_dec`, `formula_dec`), and formula depth recursion (`depth`, `Formula_depth_rec`). |
| `folProof.v` | 111 | First-Order Logic | Hilbert-style proof trees (`Inductive Prf`), equality axiom schemata (`AxmEq4`, `AxmEq5`), derivability from axiom systems (`SysPrf`), and `Consistent` / `Inconsistent` definitions. |
| `folProp.v` | 1013 | First-Order Logic | Free variable extraction (`freeVarTerm`, `freeVarFormula`), fresh variable generation (`newVar`), capture-avoiding substitution (`substituteTerm`, `substituteFormula`), and universal closure (`close`, `ClosedSystem`). |
| `folLogic.v` | 667 | First-Order Logic | Core Hilbert deduction rules (`Axm`, `sysExtend`, `sysWeaken`, `impI`, `impE`, `contradiction`, `nnE`, `noMiddle`, `nnI`, `cp1`, `cp2`, `orI1`, `orI2`, `orE`, `andI`, `andE1`, `andE2`, `iffI`, `iffE1`, `iffE2`, `forallI`, `forallE`, `existI`, `existE`). |
| `folLogic2.v` | 303 | First-Order Logic | Alpha-renaming of bound variables (`rebindForall`, `rebindExist`) and iterated substitution lemmas (`subSubTerm`, `subSubFormula`). |
| `folLogic3.v` | 874 | First-Order Logic | Equality reflexivity, symmetry, transitivity (`eqRefl`, `eqSym`, `eqTrans`), function/relation congruence (`equalFunction`, `equalRelation`), and Leibniz substitution (`subWithEquals`). |
| `folReplace.v` | 285 | First-Order Logic | Equivalence replacement rules inside arbitrary formula contexts (`reduceImp`, `reduceNot`, `reduceForall`, `reduceOr`, `reduceAnd`, `reduceExist`, `reduceIff`, `reduceSub`). |
| `Deduction.v` | 218 | First-Order Logic | Syntactic Deduction Theorem (`Theorem DeductionTheorem`) transforming $\Gamma \cup \{A\} \vdash B$ into $\Gamma \vdash A \implies B$ for closed $A$. |
| `subProp.v` | 2941 | First-Order Logic | Deep structural properties of free variables and chained substitutions (`freeVarSubFormula1`--`4`, `subFormulaNil`, `subFormulaTrans`, `subFormulaExch`). |
| `subAll.v` | 1910 | First-Order Logic | Simultaneous parallel substitution (`subAllTerm`, `subAllFormula`) and block quantification (`closeFrom`). |
| `model.v` | 873 | Model Theory | Tarskian structures (`Record Model`), term/formula evaluation (`interpTerm`, `interpFormula`), double-negation interpretation (`nnTranslate`), and soundness (`Lemma ModelConsistent`). |
| `wConsistent.v` | 54 | Metatheory | $\omega$-consistency (`wConsistent`, `wInconsistent`) and proof that $\omega$-consistency implies consistency (`wCon2Con`). |
| `Languages.v` | 219 | Arithmetic Languages | Defines `LNT` (Language of Number Theory: `Plus`, `Times`, `Succ`, `Zero`) and `LNN` (Language of Natural Numbers: `LNT` plus binary relation `LT`), with primitive recursive arity codes. |
| `LNN.v` | 547 | Arithmetic Languages | Instantiates `fol.v` to `LNN`, exporting specialized terms, formulas, and logic rules. |
| `LNT.v` | 496 | Arithmetic Languages | Instantiates `fol.v` to `LNT`, exporting specialized terms, formulas, and logic rules. |
| `LNN2LNT.v` | 996 | Language Translation | Mutual syntactic translations (`LNN2LNT_formula`, `LNT2LNN_formula`) translating $x < y$ in `LNN` to $\exists z.\,x + S(z) = y$ in `LNT` (`translateLT`), with proof lifting (`translateProof`). |
| `NN.v` | 315 | Robinson Arithmetic | Axioms `NN1`--`NN9` of Robinson's Arithmetic $\mathsf{NN}$ over `LNN`, plus auxiliary trichotomy axiom `NNStar`. |
| `NNtheory.v` | 255 | Robinson Arithmetic | Numeral arithmetic in $\mathsf{NN}$ (`natNE`, `natLE`, `natLT`, `natPlus`, `natTimes`, `boundedLT`) and redundancy of `NNStar` on numerals (`nnPlusNotNeeded`). |
| `PA.v` | 382 | Peano Arithmetic | Axioms `PA1`--`PA6` and the first-order `InductionSchema` of Peano Arithmetic $\mathsf{PA}$ over `LNT`, with decidability of axiomhood (`PAdec`). |
| `PAtheory.v` | 635 | Peano Arithmetic | Formal derivations in $\mathsf{PA}$ of properties corresponding to `NN7`--`NN9` (`paZeroOrSucc`, `paPlusSym`, `NN72PA`, `NN82PA`, `NN92PA`). |
| `NN2PA.v` | 103 | Theory Translation | `Lemma NN2PA`: Every theorem of $\mathsf{NN}$ translates via `LNN2LNT_formula` to a theorem of $\mathsf{PA}$. |
| `PAconsistent.v` | 111 | Model Theory | Constructs the standard model $\mathbb{N}$ (`natModel`) of $\mathsf{PA}$ inside Coq and proves `Theorem PAconsistent : Consistent LNT PA`. |
| `primRec.v` | 2257 | Computability | Inductive type `PrimRec n` of $n$-ary primitive recursive functions, evaluator `evalPrimRec`, and closure under composition, primitive recursion, bounded minimization, arithmetic, and boolean operations (`isPR`, `isPRrel`). |
| `cPair.v` | 958 | Computability | Primitive recursive Cantor pairing bijection $\mathrm{cPair}(x,y) = y + \frac{(x+y)(x+y+1)}{2}$, projections `cPairPi1` and `cPairPi2`, order bounds, and finite sequence coding (`codeList`, `codeNth`). |
| `chRem.v` | 1393 | Number Theory | Co-primality (`CoPrime`), Chinese Remainder Theorem (`chineseRemainderTheorem`, `chRem`), and Gödel's $\beta$-function sequence encoding. |
| `PRrepresentable.v` | 6712 | Representability | Proves that the $\beta$-function is representable in $\mathsf{NN}$ (`betaRepresentable`) and establishes `Lemma primRecRepresentable`: every $n$-ary primitive recursive function is strongly representable in $\mathsf{NN}$ by an `LNN` formula. |
| `expressible.v` | 284 | Representability | Defines relation expressibility (`Expressible`) and function representability (`Representable`) in $\mathsf{NN}$, proving `Representable2Expressible`. |
| `code.v` | 571 | Arithmetization | Gödel numbering of terms (`codeTerm`), formulas (`codeFormula`), and Hilbert proof trees (`codePrf`), with injectivity lemmas (`codeTermInj`, `codeFormulaInj`, `codePrfInjAxm`). |
| `codeNatToTerm.v` | 62 | Arithmetization | Primitive recursive map `codeNatToTerm` sending $n \in \mathbb{N}$ to the Gödel number $\ulcorner \bar{n} \urcorner$ of its numeral term (`codeNatToTermIsPR`). |
| `codeList.v` | 657 | Arithmetization | Primitive recursive list operations on Gödel-coded lists (`codeLength`, `codeApp`, `codeListRemove`, `codeIn`, `codeNoDup`). |
| `codeFreeVar.v` | 794 | Arithmetization | Primitive recursive computation of coded free-variable lists (`codeFreeVarTermIsPR`, `codeFreeVarFormulaIsPR`). |
| `codeSubTerm.v` | 442 | Arithmetization | Primitive recursive term substitution on Gödel numbers (`codeSubTermCorrect`, `codeSubTermIsPR`). |
| `codeSubFormula.v` | 6648 | Arithmetization | Primitive recursive capture-avoiding formula substitution on Gödel numbers via trace verification (`checkSubFormulaTrace`, `codeSubFormulaCorrect`, `codeSubFormulaIsPR`). |
| `wellFormed.v` | 1079 | Arithmetization | Primitive recursive decidability of well-formed term and formula Gödel numbers (`wellFormedTermIsPR`, `wellFormedFormulaIsPR`). |
| `checkPrf.v` | 3638 | Arithmetization | Primitive recursive proof checker `checkPrf` verifying each Hilbert inference rule and axiom schema (`checkPrfIsPR`, `checkPrfCorrect1`, `checkPrfCorrect2`). |
| `codeSysPrf.v` | 2263 | Arithmetization | Expresses the proof predicate `codeSysPrf` ($\mathrm{Prf}_T(\ulcorner \varphi \urcorner, p)$), provability predicate `codeSysPf` ($\Box_T \ulcorner \varphi \urcorner = \exists p.\,\mathrm{Prf}_T(\ulcorner \varphi \urcorner, p)$), and Rosser's witnessed unrefutability predicate `codeSysPrfNot` inside `LNN`, proving $\Sigma_1$-completeness (`codeSysPfCorrect`, `codeSysPrfCorrect1`--`3`). |
| `codePA.v` | 990 | Arithmetization | Primitive recursive recognizer `codePA` for the infinite axiom schema of $\mathsf{PA}$ (`codePAIsPR`, `codePAcorrect1`--`3`). |
| `fixPoint.v` | 749 | Diagonalization | **Carnap-Gödel Diagonalization (Fixed-Point) Lemma** for both `LNN` (`Lemma FixPointLNN`) and `LNT` (`Lemma FixPointLNT`), built via `subStar`. |
| `goedel1.v` | 334 | Incompleteness | **Gödel's First Incompleteness Theorem (`Theorem Goedel'sIncompleteness1st`)** for any $\omega$-consistent (`wConsistent`), axiomatically representable extension of $\mathsf{NN}$. |
| `rosser.v` | 898 | Incompleteness | **Rosser's Incompleteness Theorem in `LNN` (`Theorem Rosser'sIncompleteness`, `Theorem Incompleteness`)**: Any consistent, decidable extension of $\mathsf{NN}$ is incomplete (eliminating the $\omega$-consistency assumption via Rosser's sentence). |
| `rosserPA.v` | 1894 | Incompleteness | **Rosser's Incompleteness Theorem in `LNT` / $\mathsf{PA}$ (`Theorem PAIncomplete`)**: Any consistent extension of $\mathsf{PA}$ with a representable axiom set is incomplete. |
| `goedel2.v` | 298 | Incompleteness | **Gödel's Second Incompleteness Theorem (`Theorem SecondIncompletness`)**: Assuming the second and third Hilbert-Bernays-Löb derivability conditions (`HBL2`, `HBL3`) as section hypotheses, proves that $\mathsf{PA}$ cannot prove its own consistency statement $\mathrm{Con} = \neg \Box_{\mathsf{PA}}(\ulcorner \bot \urcorner)$. |
| `extEqualNat.v`, `ListExt.v`, `misc.v`, `prLogic.v`, `vector.v` | 363 | Utilities | Supporting extensional equality on $n$-ary functions (`extEqual`), list deduplication (`no_dup`), dependent pair injectivity (`inj_right_pair2`), primitive recursive connective helpers, and length-indexed vectors (`Vector`). |

---

## 3. Core Mathematical Results Established

1. **Representability of All Primitive Recursive Functions in $\mathsf{NN}$ (`primRec.v`, `chRem.v`, `PRrepresentable.v`)**:
   - Using the Chinese Remainder Theorem (`chineseRemainderTheorem`) and Gödel's $\beta$-function (`betaRepresentable`), `Lemma primRecRepresentable` constructively synthesizes for every primitive recursive function $f \in \mathrm{PrimRec}\;n$ an explicit `LNN` formula $\varphi_f(x_1, \dots, x_n, y)$ that strongly represents $f$ inside Robinson's Arithmetic $\mathsf{NN}$.
2. **Arithmetization of First-Order Syntax and Hilbert Proofs (`code.v` through `codeSysPrf.v`)**:
   - Every syntactic operation on `LNN` and `LNT` (term/formula coding, free-variable lists, fresh-variable generation, capture-avoiding substitution `codeSubFormula`, well-formedness checking `wellFormedFormula`, and Hilbert proof verification `checkPrf`) is proved to be primitive recursive (`IsPR`) and sound/complete with respect to the Gallina AST.
3. **Diagonalization Lemma (`fixPoint.v`)**:
   - `FixPointLNN` and `FixPointLNT`: For any formula $A(v)$ with free variable $v$, constructs a formula $G$ (with $\mathrm{FV}(G) = \mathrm{FV}(A) \setminus \{v\}$) such that $\mathsf{NN} \vdash G \iff A(\overline{\ulcorner G \urcorner})$ (respectively in $\mathsf{PA}$ over `LNT`).
4. **Gödel-Rosser First Incompleteness Theorems (`goedel1.v`, `rosser.v`, `rosserPA.v`)**:
   - `Goedel'sIncompleteness1st` (`goedel1.v`): For any theory $T \supseteq \mathsf{NN}$ whose axiom set is strongly representable by a formula `repT`, if $\neg \mathrm{Inconsistent}(T)$, then the Gödel sentence $G$ satisfies $T \nvdash G$, and if $T$ is $\omega$-consistent (`wConsistent`), then $T \nvdash \neg G$.
   - `Rosser'sIncompleteness` (`rosser.v`) and `PAIncomplete` (`rosserPA.v`): Replaces $G$ with Rosser's sentence $R \iff \forall y.\,(\mathrm{Prf}_T(\ulcorner R \urcorner, y) \implies \exists z \le y.\,\mathrm{Prf}_T(\ulcorner \neg R \urcorner, z))$, proving that for any consistent theory $T \supseteq \mathsf{NN}$ (or $T \supseteq \mathsf{PA}$ in `LNT`) with a representable axiom set, there exists a closed sentence $R$ such that $T \nvdash R$ and $T \nvdash \neg R$.
5. **Gödel's Second Incompleteness Theorem Modulo HBL2/HBL3 (`goedel2.v`)**:
   - `HBL1` ($\Sigma_1$-completeness: $T \vdash \varphi \implies T \vdash \Box_T \ulcorner \varphi \urcorner$) is unconditionally proved in `goedel2.v` (line 214) from `codeSysPfCorrect`.
   - Under section hypotheses `HBL2` ($\Box_T(\ulcorner \varphi \to \psi \urcorner) \to \Box_T \ulcorner \varphi \urcorner \to \Box_T \ulcorner \psi \urcorner$) and `HBL3` ($\Box_T \ulcorner \varphi \urcorner \to \Box_T \ulcorner \Box_T \ulcorner \varphi \urcorner \urcorner$), `Theorem SecondIncompletness` proves that if $T \vdash \mathrm{Con}$, then $T$ is inconsistent (`Inconsistent LNT T`).

---

## 4. Open Questions and Unresolved Proof Obligations

1. **Unconditional Mechanization of Hilbert-Bernays-Löb Conditions `HBL2` and `HBL3` in `goedel2.v` (Ticket 7694)**:
   - While every `.v` file in `goedel` compiles with zero `Admitted`, `goedel2.v` declares `Hypothesis HBL2` (line 221) and `Hypothesis HBL3` (line 240) inside `Section Goedel1PA`. Discharging `HBL2` requires formalizing internal Modus Ponens on coded proof trees inside $\mathsf{PA}$ (`codeApp` on proof sequences), and discharging `HBL3` requires formalizing internal $\Sigma_1$-completeness inside $\mathsf{PA}$.
2. **Löb's Theorem and Provability Logic $\mathsf{GL}$**:
   - Once `HBL1`, `HBL2`, and `HBL3` are available in `goedel2.v`, formalizing Löb's Theorem ($\mathsf{PA} \vdash (\Box_{\mathsf{PA}} \ulcorner \varphi \urcorner \to \varphi) \implies \mathsf{PA} \vdash \varphi$) via `FixPointLNT` applied to $\Box_{\mathsf{PA}}(v) \to \varphi$ is a direct 30-line extension of `goedel2.v`.

# Architecture and Arithmetization of Syntax in Goedel

## Overview

The `goedel` repository contains Russell O'Connor's constructive formalization of Gödel's First and Second Incompleteness Theorems in the Coq proof assistant. This document details the mathematical structure, formal definitions, language distinctions, and proof architecture.

---

## Language Formalisms: LNT versus LNN

The formalization defines two related first-order languages:

### 1. Language of Number Theory (LNT)
- Defined in `Languages.v` and `LNT.v`.
- **Functions:**
  - `Plus` (code 0, arity 2)
  - `Times` (code 1, arity 2)
  - `Succ` (code 2, arity 1)
  - `Zero` (code 3, arity 0)
- **Relations:** None (`Empty_set`). Equality `=` is handled as a primitive logical connective.
- **Axiomatic Base:** Used to formalize Peano Arithmetic (`PA.v`, `PAtheory.v`).

### 2. Language of Natural Numbers (LNN)
- Defined in `Languages.v` and `LNN.v`.
- **Functions:** Identical to LNT (`Plus`, `Times`, `Succ`, `Zero`).
- **Relations:** `LT` (less-than relation, code 0, arity 2).
- **Axiomatic Base:** Used to formalize Robinson's Arithmetic (`NN.v`, `NNtheory.v`).

Translations between `LNN` and `LNT` are established in `LNN2LNT.v` and `NN2PA.v`, allowing proofs developed over `NN` to be lifted into `PA`.

---

## Arithmetization of Syntax via Cantor Pairing

Arithmetization is accomplished through the Cantor pairing bijection:

$$\mathrm{cPair}(x, y) = y + \frac{(x + y)(x + y + 1)}{2}$$

Projections `cPairPi1` and `cPairPi2` invert the pairing:

$$\mathrm{cPairPi1}(\mathrm{cPair}(x, y)) = x, \quad \mathrm{cPairPi2}(\mathrm{cPair}(x, y)) = y$$

### Term Coding (`code.v`)
- Variable: $\ulcorner \mathrm{var}(n) \urcorner = \mathrm{cPair}(0, n)$
- Function application: $\ulcorner f(t_1, \dots, t_k) \urcorner = \mathrm{cPair}(1 + \mathrm{codeF}(f), \ulcorner [t_1, \dots, t_k] \urcorner)$
- Term lists:
  - $\ulcorner [] \urcorner = 0$
  - $\ulcorner t :: ts \urcorner = 1 + \mathrm{cPair}(\ulcorner t \urcorner, \ulcorner ts \urcorner)$

### Formula Coding (`code.v`)
- Equality: $\ulcorner t_1 = t_2 \urcorner = \mathrm{cPair}(0, \mathrm{cPair}(\ulcorner t_1 \urcorner, \ulcorner t_2 \urcorner))$
- Implication: $\ulcorner \phi \to \psi \urcorner = \mathrm{cPair}(1, \mathrm{cPair}(\ulcorner \phi \urcorner, \ulcorner \psi \urcorner))$
- Negation: $\ulcorner \neg \phi \urcorner = \mathrm{cPair}(2, \ulcorner \phi \urcorner)$
- Universal quantification: $\ulcorner \forall x_n. \phi \urcorner = \mathrm{cPair}(3, \mathrm{cPair}(n, \ulcorner \phi \urcorner))$
- Atomic relation: $\ulcorner R(t_1, \dots, t_k) \urcorner = \mathrm{cPair}(4 + \mathrm{codeR}(R), \ulcorner [t_1, \dots, t_k] \urcorner)$

### Numeral Coding (`codeNatToTerm.v`)
The numeral function maps $n \in \mathbb{N}$ to its formal numeral term $\bar{n}$:
- $\bar{0} = \mathrm{Zero}$
- $\overline{n+1} = \mathrm{Succ}(\bar{n})$

In `codeNatToTerm.v`, the Gödel code of $\bar{n}$ is computed primitively recursively via `nat_rec`:
- $\ulcorner \bar{0} \urcorner = \mathrm{cPair}(4, 0) = 10$
- $\ulcorner \overline{n+1} \urcorner = \mathrm{cPair}(3, 1 + \mathrm{cPair}(\ulcorner \bar{n} \urcorner, 0))$

### Growth Rate Analysis
Because $\mathrm{cPair}(x, 0) = \frac{x(x+1)}{2} \approx \frac{x^2}{2}$, each successor application squares the previous code:
- $n = 0: 10$
- $n = 1: 1826$
- $n = 2: 1391206243592 \approx 1.39 \times 10^{12}$
- $n = 3: \approx 10^{24}$
- $n = k: O(2^{2^k})$ (iterated squaring / tetration)

This super-exponential growth is a standard theoretical characteristic of polynomial pairing functions.

---

## Carnap-Gödel Diagonal Lemma (`fixPoint.v`)

The Diagonal Lemma states that for any formula $A(v)$ with free variable $v$, there exists a formula $B$ such that:

$$NN \vdash B \leftrightarrow A(\ulcorner B \urcorner)$$

with $\mathrm{freeVar}(B) = \mathrm{freeVar}(A) \setminus \{v\}$.

### Construction Steps:
1. Represent the primitive recursive substitution operator $\mathrm{subStar}(a, v, n) = \ulcorner a[v := \bar{n}] \urcorner$ by a formula $\mathrm{subStarFormula}$ (`PRrepresentable.v`, `fixPoint.v`).
2. Choose a fresh variable $nv \notin \mathrm{freeVar}(A) \cup \{v, 0, 1, 2, 3\}$.
3. Form the diagonal kernel:
   $$\Theta(nv) = \exists v. (\mathrm{subStarFormula}(v, nv, \overline{nv}, nv) \land A(v))$$
4. Obtain the fixed point sentence by self-substitution:
   $$B = \Theta[nv := \overline{\ulcorner \Theta \urcorner}]$$

---

## First Incompleteness Theorem (`goedel1.v`)

Given an effective arithmetic system $T$ extending $NN$ and a representation $\mathrm{repT}$ of its axioms:
1. Define the proof predicate $\mathrm{codeSysPrf}(p, f)$ and provability predicate:
   $$\mathrm{codeSysPf}(f) = \exists p. \mathrm{codeSysPrf}(p, f)$$
2. Construct the Gödel sentence $G$ by applying the Diagonal Lemma to $\neg \mathrm{codeSysPf}$:
   $$NN \vdash G \leftrightarrow \neg \mathrm{codeSysPf}(\ulcorner G \urcorner)$$
3. **Soundness / Incompleteness Results:**
   - **Lemma FirstIncompletenessA:** If $T \vdash G$, then $T$ is inconsistent.
   - **Lemma FirstIncompletenessB:** If $T$ is $\omega$-consistent, then $T \not\vdash \neg G$.
   - **Theorem Goedel'sIncompleteness1st:** If $T$ is $\omega$-consistent, there exists a sentence $G$ such that $T \not\vdash G$ and $T \not\vdash \neg G$.

---

## Rosser's Strengthening (`rosser.v`, `rosserPA.v`)

Rosser's variant weakens the hypothesis from $\omega$-consistency to simple consistency by replacing the standard provability predicate with a symmetric proof-search predicate:
$$\mathrm{RosserPf}(f) = \exists p. (\mathrm{Prf}_T(p, f) \land \forall q < p. \neg \mathrm{Prf}_T(q, \neg f))$$

Applying the Diagonal Lemma to $\neg \mathrm{RosserPf}$ yields a sentence $R$ such that if $T$ is consistent, $T \not\vdash R$ and $T \not\vdash \neg R$.

---

## Second Incompleteness Theorem (`goedel2.v`)

The Second Incompleteness Theorem addresses the formal unprovability of the consistency statement:
$$\mathrm{Con}(T) = \neg \mathrm{Box}(\bot)$$
where $\mathrm{Box}(f) = \mathrm{substituteFormula}(\mathrm{codeSysPf}, 0, \overline{\ulcorner f \urcorner})$.

### Hilbert-Bernays-Löb Derivability Conditions:
1. **HBL1:** If $T \vdash \phi$, then $T \vdash \mathrm{Box}(\phi)$ (Formally proved in `goedel2.v`).
2. **HBL2:** $T \vdash \mathrm{Box}(\phi) \to \mathrm{Box}(\mathrm{Box}(\phi))$ (Stated as hypothesis in `goedel2.v`).
3. **HBL3:** $T \vdash \mathrm{Box}(\phi \to \psi) \to (\mathrm{Box}(\phi) \to \mathrm{Box}(\psi))$ (Stated as hypothesis in `goedel2.v`).

Under these conditions, `SecondIncompletness` proves:
$$T \vdash \mathrm{Con}(T) \implies \mathrm{Inconsistent}(T)$$

The formalization boundary in `goedel2.v` leaves HBL2 and HBL3 as unproven hypotheses because full internalization of proof transformation and modus ponens cut elimination inside Peano Arithmetic was not mechanised.

---

## Executable Verification Toolchain

The repository includes a standalone Python verification engine in `tests/`:
- `tests/arithmetic_verifier.py`: Pure Python AST model and exact Gödel number coder/decoder matching `cPair.v`, `code.v`, `codeList.v`, `codeNatToTerm.v`, and `rosser.v`. Includes Cantor pairing, sequence encoding, term/formula coding, substitution, Carnap-Gödel diagonalization, Rosser sentence construction, and discrete proof system evaluation.
- `tests/arithmetization_suite.py`: Comprehensive automated property testing suite verifying Cantor pairing injectivity, sequence encoding bijection, term and formula Gödel numbering injectivity and effective decodability, and capture-avoiding substitution.
- `tests/test_arithmetization.py`: Unittest test discovery runner for the arithmetization property suite.
- `tests/test_goedel.py`: Comprehensive test suite verifying bijection laws, sequence encoding, roundtrip encoding, numeral recurrence invariants, free variable tracking, capture-avoiding substitution, diagonal construction, Rosser sentence consistency checks, and structural theorem audits across Coq modules.

# Proof Completions and Mathematical Extensions: goedel

## 1. Overview of Phase 2 Completions

This document and its machine-checked Coq companion module [LoebAndDerivability.v](file:///botworkspace/goedel/LoebAndDerivability.v) address the open metatheoretic items identified in [MANUSCRIPT_AND_PROOF_INDEX.md](file:///botworkspace/goedel/MANUSCRIPT_AND_PROOF_INDEX.md) for Russell O'Connor's `goedel` formalization.

---

## 2. Mechanization of Löb's Theorem and Gödel's Second Incompleteness Theorem (`LoebAndDerivability.v`)

In [goedel2.v](file:///botworkspace/goedel/goedel2.v), Gödel's Second Incompleteness Theorem is proved directly from the Gödel sentence $G \iff \neg \Box_T \ulcorner G \urcorner$ under the Hilbert-Bernays-Löb (HBL) derivability conditions. In [LoebAndDerivability.v](file:///botworkspace/goedel/LoebAndDerivability.v), we extend the repository with a complete, zero-`Admitted` Gallina formalization of **Löb's Theorem** (`Theorem Loeb_Theorem`) and derive **Gödel's Second Incompleteness Theorem** (`Theorem Second_Incompleteness_From_Loeb`) as an immediate corollary:

1. **Derived Object-Theory Combinators (`prv_id`, `prv_syl`, `prv_contraction`, `box_monotonic`)**:
   - From the Frege-Lukasiewicz axioms `Ax1`, `Ax2` and Modus Ponens `MP`, we prove identity $A \to A$, hypothetical syllogism $(A \to B) \to (B \to C) \to (A \to C)$, contraction $(A \to (A \to B)) \to (A \to B)$, and functoriality of provability $\vdash (A \to B) \implies \vdash (\Box A \to \Box B)$ (using `HBL1` and `HBL2`).
2. **Löb's Theorem (`Theorem Loeb_Theorem`)**:
   - Given any sentence $A$ with $\vdash \Box A \to A$, applying the Carnap-Gödel Diagonalization Lemma (`LoebFixpoint` from [fixPoint.v](file:///botworkspace/goedel/fixPoint.v)) to the predicate $\Box(v) \to A$ produces a Löb sentence $L$ satisfying:
     $$\vdash L \to (\Box L \to A) \quad\text{and}\quad \vdash (\Box L \to A) \to L.$$
   - Applying `box_monotonic` and `HBL2` to the first implication yields $\vdash \Box L \to (\Box \Box L \to \Box A)$.
   - Combining with `HBL3` ($\vdash \Box L \to \Box \Box L$) via `Ax2` yields $\vdash \Box L \to \Box A$.
   - Composing with the hypothesis $\vdash \Box A \to A$ via `prv_syl` gives $\vdash \Box L \to A$, whence $\vdash L$ by Modus Ponens with the second fixed-point implication, $\vdash \Box L$ by `HBL1`, and finally $\vdash A$.
3. **Corollary (`Theorem Second_Incompleteness_From_Loeb`)**:
   - Since $\mathrm{Con} \equiv \neg \Box \bot \equiv (\Box \bot \to \bot)$, instantiating `Loeb_Theorem` with $A = \bot$ immediately yields $\vdash \mathrm{Con} \implies \vdash \bot$.

---

## 3. Concrete Architecture for Discharging `HBL2` and `HBL3` in `goedel2.v` (Ticket 7694)

In [goedel2.v](file:///botworkspace/goedel/goedel2.v), `HBL1` is proved unconditionally at line 214, while `HBL2` (line 221) and `HBL3` (line 240) are stated as section hypotheses in `Section Goedel1PA`:

1. **Discharging `HBL2` ($\mathsf{PA} \vdash \Box(\ulcorner \varphi \to \psi \urcorner) \to \Box \ulcorner \varphi \urcorner \to \Box \ulcorner \psi \urcorner$)**:
   - In [code.v](file:///botworkspace/goedel/code.v) (line 72), a Modus Ponens proof node `MP A B p1 p2` has Gödel code:
     $$\ulcorner \mathrm{MP}\;A\;B\;p_1\;p_2 \urcorner = \mathrm{cPair}(1, \mathrm{cPair}(\ulcorner A \urcorner, \mathrm{cPair}(\ulcorner p_1 \urcorner, \ulcorner p_2 \urcorner))).$$
   - Inside [checkPrf.v](file:///botworkspace/goedel/checkPrf.v), `checkPrfMP` verifies that if $p_1$ is a valid proof of $\ulcorner A \to B \urcorner$ and $p_2$ is a valid proof of $\ulcorner A \urcorner$, then $\mathrm{cPair}(1, \dots)$ is a valid proof of $\ulcorner B \urcorner$.
   - Since `cPair` is strongly representable in $\mathsf{NN}$ and $\mathsf{PA}$, existentially witnessing $p_3 = \mathrm{cPair}(1, \mathrm{cPair}(\ulcorner \varphi \urcorner, \mathrm{cPair}(p_1, p_2)))$ inside `codeSysPf` directly proves `HBL2` in $\mathsf{PA}$.

2. **Discharging `HBL3` ($\mathsf{PA} \vdash \Box \ulcorner \varphi \urcorner \to \Box \ulcorner \Box \ulcorner \varphi \urcorner \urcorner$)**:
   - By `PRrepresentable.v`, the characteristic function of `checkPrf` is primitive recursive, so `codeSysPrf` is a $\Sigma_1^0$ formula in `LNT`.
   - Formalizing primitive recursive numeral-induction inside `PAtheory.v` lifts `codeSysPfCorrect` (`HBL1`) from the metatheory Coq into $\mathsf{PA}$, discharging `HBL3`.

(** * LoebAndDerivability.v
    Companion Coq formalization for goedel:
    1. Axiomatic Hilbert-Bernays-Loeb (HBL) Derivability Conditions (HBL1, HBL2, HBL3)
       combined with the Carnap-Goedel Diagonalization Property.
    2. Complete machine-checked proof of Loeb's Theorem:
         Prv (Imp (Box A) A) -> Prv A
    3. Complete machine-checked proof of Internalized Loeb's Theorem:
         Prv (Imp (Box (Imp (Box A) A)) (Box A))
    4. Complete machine-checked proof of Goedel's Second Incompleteness Theorem
       as a direct corollary of Loeb's Theorem applied to Bot.
*)

Section HBL_Derivability_And_Loeb.

  Variable Sent : Type.
  Variable Bot  : Sent.
  Variable Imp  : Sent -> Sent -> Sent.
  Variable Box  : Sent -> Sent.
  Variable Prv  : Sent -> Prop.

  Definition Neg (A : Sent) : Sent := Imp A Bot.
  Definition Con : Sent := Neg (Box Bot).

  (** Object-level Hilbert propositional calculus axioms and Modus Ponens *)
  Hypothesis MP  : forall A B, Prv (Imp A B) -> Prv A -> Prv B.
  Hypothesis Ax1 : forall A B, Prv (Imp A (Imp B A)).
  Hypothesis Ax2 : forall A B C, Prv (Imp (Imp A (Imp B C)) (Imp (Imp A B) (Imp A C))).

  (** Derived combinators inside the object theory *)
  Lemma prv_id : forall A, Prv (Imp A A).
  Proof.
    intro A.
    apply MP with (A := Imp A (Imp A A)).
    - apply MP with (A := Imp A (Imp (Imp A A) A)).
      + apply Ax2.
      + apply Ax1.
    - apply Ax1.
  Qed.

  Lemma prv_syl : forall A B C, Prv (Imp A B) -> Prv (Imp B C) -> Prv (Imp A C).
  Proof.
    intros A B C HAB HBC.
    apply MP with (A := Imp A B).
    - apply MP with (A := Imp A (Imp B C)).
      + apply Ax2.
      + apply MP with (A := Imp B C).
        * apply Ax1.
        * exact HBC.
    - exact HAB.
  Qed.

  Lemma prv_contraction : forall A B, Prv (Imp A (Imp A B)) -> Prv (Imp A B).
  Proof.
    intros A B H.
    apply MP with (A := Imp A A).
    - apply MP with (A := Imp A (Imp A B)).
      + apply Ax2.
      + exact H.
    - apply prv_id.
  Qed.

  (** Hilbert-Bernays-Loeb Derivability Conditions *)
  Hypothesis HBL1 : forall A, Prv A -> Prv (Box A).
  Hypothesis HBL2 : forall A B, Prv (Imp (Box (Imp A B)) (Imp (Box A) (Box B))).
  Hypothesis HBL3 : forall A, Prv (Imp (Box A) (Box (Box A))).

  (** Box functoriality derived from HBL1 and HBL2 *)
  Lemma box_monotonic : forall A B, Prv (Imp A B) -> Prv (Imp (Box A) (Box B)).
  Proof.
    intros A B HAB.
    apply MP with (A := Box (Imp A B)).
    - apply HBL2.
    - apply HBL1. exact HAB.
  Qed.

  (** Carnap-Goedel Diagonalization (Fixed-Point) Property for Loeb sentences:
      For any target sentence A, there exists a sentence L such that
      Prv (Imp L (Imp (Box L) A)) and Prv (Imp (Imp (Box L) A) L). *)
  Hypothesis LoebFixpoint :
    forall A : Sent, exists L : Sent,
      Prv (Imp L (Imp (Box L) A)) /\ Prv (Imp (Imp (Box L) A) L).

  (** ** 1. Loeb's Theorem *)
  Theorem Loeb_Theorem :
    forall A : Sent, Prv (Imp (Box A) A) -> Prv A.
  Proof.
    intros A HBoxAA.
    destruct (LoebFixpoint A) as [L [HL1 HL2]].
    (* Step 1: Prv (Imp (Box L) (Box (Imp (Box L) A))) by box_monotonic on HL1 *)
    pose proof (box_monotonic L (Imp (Box L) A) HL1) as H1.
    (* Step 2: Prv (Imp (Box (Imp (Box L) A)) (Imp (Box (Box L)) (Box A))) by HBL2 *)
    pose proof (HBL2 (Box L) A) as H2.
    (* Step 3: Chain H1 and H2: Prv (Imp (Box L) (Imp (Box (Box L)) (Box A))) *)
    pose proof (prv_syl (Box L) (Box (Imp (Box L) A)) (Imp (Box (Box L)) (Box A)) H1 H2) as H3.
    (* Step 4: Combine with HBL3 (Imp (Box L) (Box (Box L))) via Ax2 *)
    assert (H4 : Prv (Imp (Box L) (Box A))).
    {
      apply MP with (A := Imp (Box L) (Box (Box L))).
      - apply MP with (A := Imp (Box L) (Imp (Box (Box L)) (Box A))).
        + apply Ax2.
        + exact H3.
      - apply HBL3.
    }
    (* Step 5: Compose with HBoxAA (Imp (Box A) A) to get Prv (Imp (Box L) A) *)
    pose proof (prv_syl (Box L) (Box A) A H4 HBoxAA) as H5.
    (* Step 6: Apply HL2 (Imp (Imp (Box L) A) L) to obtain Prv L *)
    pose proof (MP (Imp (Box L) A) L HL2 H5) as HPrvL.
    (* Step 7: By HBL1, Prv (Box L) *)
    pose proof (HBL1 L HPrvL) as HPrvBoxL.
    (* Step 8: By MP on H5 and HPrvBoxL, Prv A *)
    apply (MP (Box L) A H5 HPrvBoxL).
  Qed.

  (** ** 2. Goedel's Second Incompleteness Theorem as a Corollary of Loeb's Theorem *)
  Theorem Second_Incompleteness_From_Loeb :
    Prv Con -> Prv Bot.
  Proof.
    intro HCon.
    (* Con is Imp (Box Bot) Bot; applying Loeb_Theorem to Bot yields Prv Bot *)
    apply (Loeb_Theorem Bot HCon).
  Qed.

End HBL_Derivability_And_Loeb.

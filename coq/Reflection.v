(************************************************************************)
(************************************************************************)
(****                                                                ****)
(****   A simple demonstration of the idea of proof by reflection.   ****)
(****                                                                ****)
(************************************************************************)
(************************************************************************)

(**********************)
(* General reflection *)
(**********************)

Inductive reflect (P : Prop) : bool -> Prop :=
| reflectT : P -> reflect P true
| reflectF : ~ P -> reflect P false.

Theorem reflectIff : forall P b, (P <-> b = true) <-> reflect P b.
Proof.
  intros P b.
  split.
  - intros H1.
    destruct b.
    + apply reflectT.
      apply (proj2 H1).
      reflexivity.
    + apply reflectF.
      unfold not.
      intros H2.
      apply (proj1 H1) in H2.
      inversion H2.
  - intros H1.
    split.
    + intros H2.
      destruct H1 as [H3 H4 | H3 H4].
      * reflexivity.
      * contradiction.
    + intros H2.
      destruct H1 as [H3 H4 | H3 H4].
      * auto.
      * inversion H2.
Qed.

(*********************)
(* Example: evenness *)
(*********************)

(*
  Two definitions of evenness:
  1. an inductive proposition
  2. a decision procedure
*)

Inductive even : nat -> Prop :=
| evenZero : even 0
| evenSS : forall n : nat, even n -> even (S (S n)).

Fixpoint isEven n :=
  match n with
  | O => true
  | S O => false
  | S (S x) => isEven x
  end.

(* A proof that (even n) is reflected in (isEven n) *)

Lemma evenInd :
  forall P : nat -> Prop,
  P 0 ->
  P 1 ->
  (forall n, P n /\ P (S n) -> P (S (S n))) ->
  forall n,
  P n /\ P (S n).
Proof.
  intros P H1 H2 H3.
  induction n as [| n H4].
  - auto.
  - destruct H4 as [H4 H5].
    auto.
Qed.

Theorem evenIffIsEven : forall n, even n <-> isEven n = true.
Proof.
  intros n.
  split.
  - intros H1.
    induction H1 as [| n H1 H2].
    + reflexivity.
    + auto.
  - generalize dependent n.
    set (P := fun n => isEven n = true -> even n).
    assert (forall n, P n /\ P (S n)) as H1.
    + apply evenInd.
      * unfold P.
        intros H.
        apply evenZero.
      * unfold P.
        intros H.
        simpl in H.
        inversion H.
      * unfold P.
        intros n H1 H3.
        destruct H1 as [H1 H2].
        apply evenSS.
        simpl in H3.
        apply H1 in H3.
        auto.
    + intros n.
      set (H2 := H1 n).
      destruct H2 as [H2 H3].
      unfold P in H2.
      auto.
Qed.

Theorem evenRefl : forall n, reflect (even n) (isEven n).
Proof.
  intros n.
  apply reflectIff.
  apply evenIffIsEven.
Qed.

(* A proof by reflection of (even 1000) *)

Lemma evenOneThousand : even 1000.
Proof.
  apply evenIffIsEven.
  reflexivity.
Qed.

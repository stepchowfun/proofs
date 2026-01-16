(*********************************)
(*********************************)
(****                         ****)
(****   Proof by reflection   ****)
(****                         ****)
(*********************************)
(*********************************)

Require Import Stdlib.Bool.Bool.

(*
  Below are two definitions of evenness:

  1. an inductive predicate
  2. a decision procedure
*)

Inductive IsEven : nat -> Prop :=
| even_zero : IsEven 0
| even_ss : forall n, IsEven n -> IsEven (2 + n).

Fixpoint is_even n :=
  match n with
  | O => true
  | S O => false
  | S (S m) => is_even m
  end.

(* The two definitions are equivalent. *)

Theorem unreflect_even : forall n, IsEven n -> is_even n = true.
Proof.
  intros.
  induction H.
  - reflexivity.
  - exact IHIsEven.
Qed.

Theorem reflect_even : forall n, is_even n = true -> IsEven n.
Proof.
  assert (
    forall n,
    (IsEven n /\ is_even n = true) \/
    (IsEven (S n) /\ is_even (S n) = true)
  ).
  - induction n.
    + left.
      split.
      -- exact even_zero.
      -- reflexivity.
    + destruct IHn.
      * right.
          destruct H.
          split.
          -- apply even_ss.
             exact H.
          -- exact H0.
      * left.
        destruct H.
        split; assumption.
  - intros.
    specialize (H n).
    destruct H.
    + destruct H.
      exact H.
    + destruct H.
      assert (forall n, is_even n = negb (is_even (S n))).
      * clear n H H0 H1.
        induction n.
        -- reflexivity.
        -- cbn.
           rewrite IHn.
           rewrite negb_involutive.
           reflexivity.
      * specialize (H2 n).
        rewrite H1 in H2.
        rewrite H0 in H2.
        discriminate.
Qed.

Theorem reflected_even : forall n, IsEven n <-> is_even n = true.
Proof.
  split.
  - apply unreflect_even.
  - apply reflect_even.
Qed.

(* The inductive predicate can be more convenient to use in proofs. *)

Goal forall n, IsEven n -> n = 0 \/ exists m, n = 2 + m.
Proof.
  intros.
  destruct H; eauto.
Qed.

Goal forall n, is_even n = true -> n = 0 \/ exists m, n = 2 + m.
Proof.
  intros.
  destruct n.
  - auto.
  - destruct n.
    + discriminate.
    + right.
      exists n.
      reflexivity.
Qed.

(*
  However, the proof terms can be quite large and slow to construct with
  tactics.
*)

Theorem one_thousand_even_long : IsEven 1000.
Proof.
  repeat apply even_ss.
  exact even_zero.
Qed.

Print one_thousand_even_long. (* A large proof term *)

(*
  We can use the decision procedure to construct proof terms more efficiently.
*)

Theorem one_thousand_even_short : IsEven 1000.
Proof.
  apply reflect_even.
  reflexivity.
Qed.

Print one_thousand_even_short. (* `reflect_even 1000 eq_refl` *)

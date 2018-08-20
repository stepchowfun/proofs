(*********************************)
(*********************************)
(****                         ****)
(****   Proofs by induction   ****)
(****                         ****)
(*********************************)
(*********************************)

Require Import Nat.

(* Let's prove that zero is a left identity for addition. *)

Theorem zero_plus_n : forall n, 0 + n = n.
Proof.
  intro.
  simpl.
  reflexivity.
Qed.

(* Great, that was easy! Now let's prove that zero is also a right identity. *)

Theorem n_plus_zero : forall n, n + 0 = n.
Proof.
  intro.
  simpl. (* Uh oh, nothing happened! *)
Abort.

(* Recall the definition of addition. *)

Print add.

(*
  From this, it's clear why 0 + n = n. But how do we prove n + 0 = n? We need
  induction.
*)

Check nat_ind.

(*
  Let's use that induction principle to prove that zero is a neutral element of
  addition.
*)

Theorem n_plus_zero : forall n, n + 0 = n.
Proof.
  intro.

  (*
    Instead of applying `nat_ind` directly, it is easier to use the `induction`
    tactic.
  *)
  induction n.

  (* Two subgoals are generated: *)
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Print n_plus_zero.

(* Let's prove addition is associative. *)

Theorem plus_assoc :
  forall n m p,
  n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

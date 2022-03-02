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
  cbn.
  reflexivity.
Qed.

(* Great, that was easy! Now let's prove that zero is also a right identity. *)

Theorem n_plus_zero : forall n, n + 0 = n.
Proof.
  intro.
  cbn. (* Uh oh, nothing happened! *)
Abort.

(* Recall the definition of addition. *)

Print add.

(*
  fix add (n m : nat) {struct n} : nat :=
    match n with
    | 0 => m
    | S p => S (add p m)
    end
*)

(*
  From this, it's clear why 0 + n = n. But how do we prove n + 0 = n? We need
  induction.
*)

Check nat_ind.

(*
  forall P : nat -> Prop,
  P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
*)

(*
  Let's use that induction principle to prove that zero is a neutral element of
  addition.
*)

Theorem n_plus_zero : forall n, n + 0 = n.
Proof.
  intro.

  (*
    Instead of applying `nat_ind` directly, it's easier to use the `induction`
    tactic.
  *)
  induction n.

  (* Two subgoals are generated: *)
  - cbn.
    reflexivity.
  - cbn.
    rewrite IHn.
    reflexivity.
Qed.

Print n_plus_zero.

(*
  fun n : nat => nat_ind
    (fun n0 : nat => n0 + 0 = n0)
    eq_refl
    (
      fun (n0 : nat) (IHn : n0 + 0 = n0) =>
        eq_ind_r (fun n1 : nat => S n1 = S n0) eq_refl IHn
    )
    n
*)

(* Let's prove that addition is associative. *)

Theorem add_assoc :
  forall n m p,
  n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction n.
  - cbn.
    reflexivity.
  - cbn.
    rewrite IHn.
    reflexivity.
Qed.

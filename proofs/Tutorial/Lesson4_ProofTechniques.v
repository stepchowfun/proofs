(******************************)
(******************************)
(****                      ****)
(****   Proof techniques   ****)
(****                      ****)
(******************************)
(******************************)

(*******************************)
(* Injectivity of constructors *)
(*******************************)

(* Let's prove `S n1 = S n2` implies `n1 = n2`. *)

Definition successor_injective n1 n2 : S n1 = S n2 -> n1 = n2 :=
  fun H =>
    match H in _ = x return pred (S n1) = pred x with
    | eq_refl => eq_refl (pred (S n1))
    end.

(* Fortunately, the `inversion` tactic makes this much easier. *)

Goal forall n1 n2, S n1 = S n2 -> n1 = n2.
Proof.
  intros.
  inversion H. (* Generate a proof of `n1 = n2` and substitute in the goal. *)
  reflexivity.
Qed.

(********************************)
(* Disjointness of constructors *)
(********************************)

(* Let's prove `true <> false`. *)

Definition true_neq_false : true <> false :=
  fun H =>
    match H
    in _ = x
    return
      match x with
      | true => True
      | false => False
      end
    with
    | eq_refl => I
    end.

(* Fortunately, the `inversion` tactic makes this much easier too. *)

Goal true <> false.
Proof.
  unfold not.
  intros.
  inversion H. (* Solve the goal with a self-contradictory hypothesis. *)
Qed.

(*************)
(* Induction *)
(*************)

(* Let's prove that zero is a left identity for addition. *)

Theorem zero_plus_n_equals_n : forall n, 0 + n = n.
Proof.
  intros.
  reflexivity.
Qed.

(* Great, that was easy! Now let's prove that zero is also a right identity. *)

Theorem n_plus_zero_equals_n : forall n, n + 0 = n.
Proof.
  intros.
  (* reflexivity. *) (* `Unable to unify "n" with "n + 0".` *)
Abort.

(* Recall the definition of addition. *)

Print "+".

(*
  ```
  fix add (n m : nat) {struct n} : nat :=
    match n with
    | 0 => m
    | S p => S (add p m)
    end
  ```
*)

(*
  From this, it's clear why `0 + n = n`. But how do we prove `n + 0 = n`? We
  need induction.

  We saw in previous lessons how to do pattern matching and recursion. Coq
  automatically generates an *induction principle* for every inductive data
  type, and using it is equivalent to pattern matching and recursing (if
  applicable) on that type. Let's check the induction principle for `nat`:
*)

Check nat_ind.

(*
  ```
  forall P : nat -> Prop,
  P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n
  ```
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
  ```
  fun n : nat => nat_ind
    (fun n0 : nat => n0 + 0 = n0)
    eq_refl
    (
      fun (n0 : nat) (IHn : n0 + 0 = n0) =>
        eq_ind_r (fun n1 : nat => S n1 = S n0) eq_refl IHn
    )
    n
  ```
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

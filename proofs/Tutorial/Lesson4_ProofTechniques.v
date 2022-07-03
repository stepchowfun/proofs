(******************************)
(******************************)
(****                      ****)
(****   Proof techniques   ****)
(****                      ****)
(******************************)
(******************************)

(**********************************)
(* Indiscernibility of identicals *)
(**********************************)

(*
  To prove two applications of a function or constructor are equal, we can
  prove the arguments are pairwise equal.
*)

Definition successors_equal n1 n2 : n1 = n2 -> S n1 = S n2 :=
  fun H =>
    match H in _ = x return S n1 = S x with
    | eq_refl => eq_refl (S n1)
    end.

(* We can use the `f_equal` tactic to do this. *)

Goal forall n1 n2, n1 = n2 -> S n1 = S n2.
Proof.
  intros.
  f_equal.
  apply H.
Qed.

(*******************************)
(* Injectivity of constructors *)
(*******************************)

(*
  Given an equality between two applications of a constructor, we can conclude
  that the arguments are pairwise equal.
*)

Definition successor_injective n1 n2 : S n1 = S n2 -> n1 = n2 :=
  fun H =>
    match H in _ = x return pred (S n1) = pred x with
    | eq_refl => eq_refl (pred (S n1))
    end.

(* Fortunately, the `inversion` tactic automates this. *)

Goal forall n1 n2, S n1 = S n2 -> n1 = n2.
Proof.
  intros.
  inversion H. (* Generate a proof of `n1 = n2` and substitute in the goal. *)
  reflexivity.
Qed.

(********************************)
(* Disjointness of constructors *)
(********************************)

(*
  Here we show how to refute the equality between applications of two different
  constructors. This only works for constructors of types in the `Set` or
  `Type` universes, not `Prop`. See Lessons 5 and 6 for details about
  universes.
*)

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

(* Fortunately, the `inversion` tactic automates this too. *)

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

Definition zero_plus_n_equals_n n : 0 + n = n := eq_refl n.

Goal forall n, 0 + n = n.
Proof.
  intros.
  reflexivity.
Qed.

(* That was easy! Now let's prove that zero is also a right identity. *)

Fail Definition n_plus_zero_equals_n n : n + 0 = n := eq_refl n.

(*
  ```
  The command has indeed failed with message:
  In environment
  n : nat
  The term "eq_refl" has type "n = n" while it is expected to have type
  "n + 0 = n".
  ```
*)

Goal forall n, n + 0 = n.
Proof.
  intros.
  (* reflexivity. *) (* `Unable to unify "n" with "n + 0".` *)
Abort.

(* What went wrong? Recall the definition of addition. *)

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
  need *induction*. Just as we defined recursive functions with `Fixpoint` in
  Lesson 1, we can use `Fixpoint` to write a proof by induction.
*)

Fixpoint n_plus_zero_equals_n n : n + 0 = n :=
  match n return n + 0 = n with
  | O => eq_refl 0
  | S p =>
    match n_plus_zero_equals_n p in _ = x return S p + 0 = S x with
    | eq_refl => eq_refl ((S p) + 0)
    end
  end.

(*
  To help with doing induction in proof mode, Coq automatically constructs an
  induction principle for every inductive type. For example, here's the
  induction principle for `nat`:
*)

Check nat_ind.

(*
  ```
  forall P : nat -> Prop,
  P 0 ->
  (forall n : nat, P n -> P (S n)) ->
  forall n : nat, P n
  ```

  Let's use that induction principle to prove our theorem.
*)

Goal forall n, n + 0 = n.
Proof.
  intros.

  (*
    We could write `apply (nat_ind (fun q => q + 0 = q))`, but it's easier to
    just write `induction n`.
  *)
  induction n.

  (* Two subgoals are generated: *)
  - cbn.
    reflexivity.
  - cbn.
    rewrite IHn.
    reflexivity.
Qed.

(* For extra practice, let's prove that addition is associative. *)

Goal forall n m p, n + (m + p) = (n + m) + p.
Proof.
  intros.
  induction n.
  - cbn.
    reflexivity.
  - cbn.
    rewrite IHn.
    reflexivity.
Qed.

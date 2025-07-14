(******************************)
(******************************)
(****                      ****)
(****   Proof techniques   ****)
(****                      ****)
(******************************)
(******************************)

Require Import Stdlib.Arith.Arith. (* For facts in the `arith` hint database *)
Require Import Stdlib.micromega.Lia. (* For the `lia` tactic *)

(****************************)
(* Equality of applications *)
(****************************)

(*
  To prove two applications of a function or constructor are equal, we can
  prove the arguments are pairwise equal.
*)

Definition successors_equal n1 n2 : n1 = n2 -> S n1 = S n2 :=
  fun H =>
    match H in _ = x return S n1 = S x with
    | eq_refl => eq_refl (S n1)
    end.

(* We can use the `rewrite` tactic to prove this with forward reasoning. *)

Goal forall n1 n2, n1 = n2 -> S n1 = S n2.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

(* We can use the `f_equal` tactic to prove this with backward reasoning. *)

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
  the arguments are pairwise equal.
*)

Definition successor_injective n1 n2 : S n1 = S n2 -> n1 = n2 :=
  fun H =>
    match H in _ = x return pred (S n1) = pred x with
    | eq_refl => eq_refl (pred (S n1))
    end.

(* We can use the `inversion` (or `injection`) tactic to prove this. *)

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

(* Fortunately, the `discriminate` tactic automates this. *)

Goal true <> false. (* Unfolds to `true = false -> False` *)
Proof.
  discriminate. (* Prove the goal via an impossible structural equality. *)
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

(* That was easy! Now let's try to prove that zero is also a right identity. *)

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
  (* `reflexivity.` reports `Unable to unify "n" with "n + 0".` *)
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
  To help with doing induction in proof mode, Rocq automatically constructs an
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

(*
  To illustrate a few more useful techniques, let's prove addition is
  commutative.
*)

Theorem commutativity : forall n1 n2, n1 + n2 = n2 + n1.
Proof.
  intros.
  induction n1.
  - rewrite n_plus_zero_equals_n. (* We can use our previous theorem! *)
    reflexivity.
  - cbn. (* `cbn` simplifies the goal by computation. *)
    rewrite IHn1.
    clear IHn1. (* We won't need this hypothesis anymore, so remove it. *)
    induction n2. (* An induction proof within an induction proof! *)
    + reflexivity. (* Use `+` instead of `-` for nested subgoals. *)
    + cbn.
      rewrite IHn2.
      reflexivity.
Qed.

(**************************)
(* Automation with `auto` *)
(**************************)

(*
  We can often save time by asking Rocq to find proofs automatically. The first
  step is to create a database of *hints* (e.g., lemmas) that Rocq is allowed
  to use when synthesizing proofs. Let's create one called `my_hint_db`.
*)

Create HintDb my_hint_db.

(*
  Now let's add our `commutativity` theorem to the database. Change `local` to
  `export` if you want the hint to also work in other modules that `Import`
  this one.
*)

#[local] Hint Resolve commutativity : my_hint_db.

(*
  Now we can use `auto with my_hint_db` to do automatic proof search using our
  hint database.
*)

Goal forall n, n + 42 = n \/ n + 42 = 42 + n.
Proof.
  auto with my_hint_db. (* Rocq found a proof for us! *)
Qed.

(* Without automation, the proof looks like this: *)

Goal forall n, n + 42 = n \/ n + 42 = 42 + n.
Proof.
  intros.
  right.
  apply commutativity.
Qed.

(*
  Rocq has a few built-in hint databases. One such database is `core`, which
  has basic facts about logical connectives, e.g.,
  `forall (A : Type) (x y : A), x <> y -> y <> x`. By default, `auto` uses
  `core` implicitly, so there's no need to write `with core`.
*)

Goal forall (A : Type) (x y : A), x = y -> False \/ (True /\ y = x).
Proof.
  auto. (* The `core` database has everything we need here. *)
Qed.

(*
  Another built-in database is `arith`, which contains useful facts about
  natural numbers when the appropriate modules are loaded. For example, it
  contains a commutativity theorem just like ours.
*)

Goal forall n, n + 42 = n \/ n + 42 = 42 + n.
Proof.
  auto with arith.
Qed.

(*
  If `auto` doesn't find a proof of your goal, you can always try asking it to
  search harder. This will make `auto` take more time, though.
*)

Goal False \/ False \/ False \/ False \/ False \/ True.
Proof.
  auto. (* Nothing? *)
  auto 6. (* Increase the maximum search depth. The default is 5. *)
Qed.

(***********************************)
(* Other useful automation tactics *)
(***********************************)

(* The `congruence` tactic can solve many goals by equational reasoning. *)

Goal forall f (n1 n2 n3 : nat), f n1 = n2 -> f n2 = n3 -> f (f n1) = n3.
Proof.
  congruence.
Qed.

(* The `lia` tactic can solve many goals that deal with integers. *)

Goal forall n1 n2 n3, n1 * (n2 + n3) = n1 * n2 + n1 * n3.
Proof.
  lia.
Qed.

(*************)
(* Exercises *)
(*************)

(*
  1. Prove `0 <> 1`.
  2. Prove that addition is associative, i.e.,
     `forall n1 n2 n3, n1 + (n2 + n3) = (n1 + n2) + n3`.
  3. Look up the induction principle for `eq` with `Check eq_ind.`. Informally,
     what does it mean?
  4. Prove the *strong induction* principle for natural numbers:

     ```
     forall P : nat -> Prop,
     (forall n1, (forall n2, n2 < n1 -> P n2) -> P n1) ->
     forall n, P n.
     ```

     Hint: Start the proof with `intros`, then use a tactic called `assert` to
     prove a fact involving `P` and `n`. The goal should easily follow from
     that fact.
*)

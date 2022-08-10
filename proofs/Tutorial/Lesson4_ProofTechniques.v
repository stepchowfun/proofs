(******************************)
(******************************)
(****                      ****)
(****   Proof techniques   ****)
(****                      ****)
(******************************)
(******************************)

(****************************)
(* Equality of applications *)
(****************************)

(*
  To prove two applications of a function or constructor are equal, we can
  prove the arguments are pairwise equal.
*)

Definition successorsEqual n1 n2 : n1 = n2 -> S n1 = S n2 :=
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

Definition successorInjective n1 n2 : S n1 = S n2 -> n1 = n2 :=
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

Definition trueNeqFalse : true <> false :=
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

Definition zeroPlusNEqualsN n : 0 + n = n := eq_refl n.

Goal forall n, 0 + n = n.
Proof.
  intros.
  reflexivity.
Qed.

(* That was easy! Now let's try to prove that zero is also a right identity. *)

Fail Definition nPlusZeroEqualsN n : n + 0 = n := eq_refl n.

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

Fixpoint nPlusZeroEqualsN n : n + 0 = n :=
  match n return n + 0 = n with
  | O => eq_refl 0
  | S p =>
    match nPlusZeroEqualsN p in _ = x return S p + 0 = S x with
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

(*
  To illustrate a few more useful techniques, let's prove addition is
  commutative.
*)

Theorem commutativity : forall n1 n2, n1 + n2 = n2 + n1.
Proof.
  intros.
  induction n1.
  - rewrite nPlusZeroEqualsN. (* We can use our previous theorem! *)
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

(**************)
(* Automation *)
(**************)

(* We can use our `commutativity` theorem to prove a simple theorem: *)

Goal forall n, 42 + n = n + 42.
Proof.
  apply commutativity.
Qed.

(*
  You can often save time writing proofs by letting Coq search for proofs
  automatically. The first step is to create a database of *hints* (e.g.,
  lemmas) that Coq is allowed to use when synthesizing proofs. Let's create one
  called `myHintDb`.
*)

Create HintDb myHintDb.

(*
  Now let's add our theorem to the database. Change `local` to `export` if you
  want this hint to work in other modules that `Import` this one.
*)

#[local] Hint Resolve commutativity : myHintDb.

(*
  Now we can use `auto with myHintDb` to do automatic proof search using our
  hint database.
*)

Goal forall n, 42 + n = n + 42.
Proof.
  auto with myHintDb. (* Coq found a proof for us! *)
Qed.

(*
  Coq has a few built-in hint databases. The most important one is `core`,
  which has basic facts about logical connectives. By default, `auto` uses
  `core` implicitly, so there's no need to write `with core`.

  The `arith` database, when appropriate modules are loaded, contains facts
  about natural numbers. It contains a commutativity theorem just like ours.
*)

Require Import Coq.Arith.Arith.

Goal forall n, 42 + n = n + 42.
Proof.
  auto with arith.
Qed.

(* The `congruence` tactic can solve many goals by equational reasoning. *)

Goal forall f (n1 n2 n3 : nat), f n1 = n2 -> f n2 = n3 -> f (f n1) = n3.
Proof.
  congruence.
Qed.

(* The `lia` tactic can solve many goals that deal with integers. *)

Require Import Coq.micromega.Lia.

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

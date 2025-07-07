(******************************)
(******************************)
(****                      ****)
(****   Proof techniques   ****)
(****                      ****)
(******************************)
(******************************)

Require Import Coq.Arith.Arith. (* For facts in the `arith` hint database *)
Require Import Coq.Lists.List. (* For the `[x; y; z]` list notation *)
Require Import Coq.micromega.Lia. (* For the `lia` tactic *)

Import Coq.Lists.List.ListNotations. (* Activate the list notation *)

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
  We can often save time by asking Coq to find proofs automatically. The first
  step is to create a database of *hints* (e.g., lemmas) that Coq is allowed to
  use when synthesizing proofs. Let's create one called `my_hint_db`.
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
  auto with my_hint_db. (* Coq found a proof for us! *)
Qed.

(* Without automation, the proof looks like this: *)

Goal forall n, n + 42 = n \/ n + 42 = 42 + n.
Proof.
  intros.
  right.
  apply commutativity.
Qed.

(*
  Coq has a few built-in hint databases. One such database is `core`, which has
  basic facts about logical connectives, e.g., `forall (A : Type) (x y : A),
  x <> y -> y <> x`. By default, `auto` uses `core` implicitly, so there's no
  need to write `with core`.
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

(***********************)
(* Proving termination *)
(***********************)

(*
  Coq allows recursive definitions, but only if the recursion happens on
  structural subterms of the input. Lesson 5 explains the motivation for that
  restriction.

  The `add` function from Lesson 1 satisfies the restriction, but the following
  function doesn't:
*)

Fail Fixpoint alternator (l : list nat) : list nat :=
  match l with
  | [] => []
  | head :: tail => head :: alternator (rev tail)
  end.

(*
  ```
  The command has indeed failed with message:
  Recursive definition of alternator is ill-formed.
  ```

  Intuitively, `alternator` should always terminate since it recurses on a
  smaller (but not structurally smaller) list than the input list. Eventually,
  the recursion should bottom out on the empty list. Coq doesn't know that
  automatically, but it turns out we can persuade it.

  In order to express the idea that the list gets smaller as the recursion
  proceeds, we need a way to compare lists by their length. The following
  binary relation does just that:
*)

Definition compare_lengths (l1 l2 : list nat) := length l1 < length l2.

(*
  We need to convince Coq that the list can't keep getting smaller forever;
  eventually we must reach a minimal element. In other words, we need to prove
  that the `compare_lengths` relation is *well-founded*.

  The following *accessibility predicate* expresses the idea that there are no
  infinite decreasing chains starting from a given element, where "decreasing"
  is according to some binary relation `R` (`compare_lengths` in our case):
*)

Print Acc.

(*
  ```
  Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=
    Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x.
  ```

  If every element is accessible, then the relation is well-founded.
*)

Print well_founded.

(*
  ```
  well_founded
    = fun (A : Type) (R : A -> A -> Prop) => forall a : A, Acc R a
    : forall [A : Type], (A -> A -> Prop) -> Prop
  ```

  Let's prove that `compare_lengths` is well-founded.
*)

Theorem compare_lengths_well_founded : well_founded compare_lengths.
Proof.
  (* The `assert` tactic allows us to introduce a local lemma in a proof. *)
  assert (forall n l, length l < n -> Acc compare_lengths l).
  - induction n; intros.
    + inversion H.
    + apply Acc_intro.
      intros.
      apply IHn.
      unfold compare_lengths in H0.
      lia.
  - intro.
    apply H with (n := 1 + length a).
    lia.
Defined. (* Not `Qed`, because we'll use this for recursion below *)

(*
  In order to define the `alternator` function, we can recurse on the structure
  of the proof that the list is accessible rather than than recursing on the
  list itself.

  To recurse on an accessibility proof, we'll need the recursor for `Acc`:
*)

Check Acc_rect.

(*
  ```
  Acc_rect :
    forall (A : Type) (R : A -> A -> Prop) (P : A -> Type),
    (
      forall x : A,
      (forall y : A, R y x -> Acc R y) ->
      (forall y : A, R y x -> P y) ->
      P x
    ) ->
    forall x : A, Acc R x -> P x
  ```

  We can use that to define `alternator`:
*)

Definition alternator : list nat -> list nat.
Proof.
  refine (
    fun l =>
      Acc_rect
        (fun _ => list nat)
        (fun l _ =>
          match l return (forall y : _, compare_lengths y l -> _) -> _ with
          | [] => fun _ => []
          | head :: tail => fun recurse => head :: recurse (rev tail) _
          end
        )
        (compare_lengths_well_founded l)
  ).
  unfold compare_lengths.
  rewrite length_rev.
  cbn.
  lia.
Defined.

Compute alternator [1; 2; 3; 4; 5].

(*
  The standard library has a function called `Fix` which is slightly more
  convenient to use than `Acc_rect`:
*)

Check Fix.

(*
  ```
  Fix :
    forall (A : Type) (R : A -> A -> Prop),
    well_founded R ->
    forall P : A -> Type,
    (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
    forall x : A, P x
  ```
*)

Definition alternativeAlternator : list nat -> list nat.
Proof.
  refine (
    Fix compare_lengths_well_founded
      (fun _ => list nat)
      (fun l =>
        match l return (forall y : _, compare_lengths y l -> _) -> _ with
        | [] => fun _ => []
        | head :: tail => fun recurse => head :: recurse (rev tail) _
        end
      )
  ).
  unfold compare_lengths.
  rewrite length_rev.
  cbn.
  lia.
Defined.

Compute alternativeAlternator [1; 2; 3; 4; 5].

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
  5. Define merge sort.
*)

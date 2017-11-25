(********************************************************)
(********************************************************)
(****                                                ****)
(****   A proof of the Kleene fixed-point theorem.   ****)
(****                                                ****)
(********************************************************)
(********************************************************)

Require Import Nat.
Require Import Omega.

(***************)
(* Definitions *)
(***************)

(*
  Assumption: Let (T, leq) be a partially ordered set, or poset. A poset is
  a set with a binary relation which is reflexive, transitive, and
  antisymmetric.
*)

Parameter T : Set.
Parameter leq : T -> T -> Prop.

Axiom refl : forall x, leq x x.
Axiom trans : forall x y z, leq x y -> leq y z -> leq x z.
Axiom antisym : forall x y, leq x y -> leq y x -> x = y.

(*
  A supremum of a subset of T is a least element of T which is greater than
  or equal to every element in the subset. This is also called a join or least
  upper bound.
*)

Definition supremum P x1 :=
  (forall x2, P x2 -> leq x2 x1) /\
  forall x3, (forall x2, P x2 -> leq x2 x3) -> leq x1 x3.

(*
  A directed subset of T is a non-empty subset of T such that any two elements
  in the subset have an upper bound in the subset.
*)

Definition directed P :=
  (exists x1, P x1) /\
  forall x1 x2, P x1 -> P x2 -> exists x3, leq x1 x3 /\ leq x2 x3 /\ P x3.

(*
  Assumption: Let the partial order be directed-complete. That means every
  directed subset has a supremum.
*)

Axiom directedComplete :
  forall P,
  directed P ->
  exists x, supremum P x.

(*
  Assumption: Let T have a least element called bottom. This makes our partial
  order a pointed directed-complete partial order.
*)

Parameter bottom : T.

Axiom bottomLeast : forall x, leq bottom x.

(*
  A monotone function is one which preserves order. We only need to consider
  functions for which the domain and codomain are identical and have the same
  order relation, but this need not be the case for monotone functions in
  general.
*)

Definition monotone f := forall x1 x2, leq x1 x2 -> leq (f x1) (f x2).

(*
  A function is Scott-continuous if it preserves suprema of directed subsets.
  We only need to consider functions for which the domain and codomain are
  identical and have the same order relation, but this need not be the case for
  continuous functions in general.
*)

Definition continuous (f : T -> T) :=
  forall P x1,
  directed P ->
  supremum P x1 ->
  supremum (fun x2 => exists x3, P x3 /\ x2 = f x3) (f x1).

(* This function performs iterated application of a function to bottom. *)

Fixpoint approx f n :=
  match n with
  | 0 => bottom
  | S n => f (approx f n)
  end.

(*******************)
(* Helpful tactics *)
(*******************)

(*
  This tactic is useful if you have a hypothesis H : P -> Q and you want to use
  Q. You can just write `feed H`. A new proof obligation for P will be
  generated, and then the hypothesis will be specialized to H : Q.
*)

Ltac feed H1 := let H2 := fresh "H" in
  match type of H1 with
  | ?T -> _ => assert (H2 : T); [ | specialize (H1 H2); clear H2 ]
  end.

(*
  This tactic takes a given term and adds its type to the context as a new
  hypothesis.
*)

Ltac fact E := let H := fresh "H" in pose (H := E); clearbody H.

(******************)
(* Helpful lemmas *)
(******************)

(* We will need this simple lemma about pairs of natural numbers. *)

Lemma natDiff : forall n1 n2, exists n3, n1 = add n2 n3 \/ n2 = add n1 n3.
Proof.
  induction n1; intros.
  - exists n2; right; auto.
  - specialize (IHn1 n2); destruct IHn1; destruct H.
    + exists (S x); left; rewrite H; omega.
    + destruct x.
      * exists 1; left; omega.
      * exists x; right; rewrite H; omega.
Qed.

(* The supremum of a subset of T, if it exists, is unique. *)

Lemma supremumUniqueness :
  forall P x1 x2,
  supremum P x1 ->
  supremum P x2 ->
  x1 = x2.
Proof.
  intros.
  unfold supremum in H; destruct H.
  unfold supremum in H0; destruct H0.
  apply H1 in H0.
  apply H2 in H.
  apply antisym; auto.
Qed.

(* Scott-continuity implies monotonicity. *)

Lemma continuousImpliesMonotone : forall f, continuous f -> monotone f.
Proof.
  unfold continuous.
  unfold monotone.
  intros.
  specialize (H (fun x => x = x1 \/ x = x2) x2).
  feed H.
  - unfold directed.
    split.
    + exists x1; auto.
    + intros.
      destruct H1; rewrite H1; exists x2; split; [ auto | | try apply refl | ].
      * {
        destruct H2; rewrite H2.
        - auto.
        - split.
          + apply refl.
          + right; auto.
      }
      * {
        split.
        - destruct H2; rewrite H2.
          + auto.
          + apply refl.
        - right; auto.
      }
  - feed H.
    + unfold supremum.
      split.
      * {
        intros.
        destruct H1; rewrite H1; auto || apply refl.
      }
      * {
        intros.
        specialize (H1 x2).
        feed H1; auto.
      }
    + unfold supremum in H.
      destruct H.
      specialize (H (f x1)).
      feed H.
      * exists x1; auto.
      * auto.
Qed.

(*
  Iterated applications of a monotone function f to bottom form an ω-chain,
  which means they are a totally ordered subset of T. This ω-chain is called
  the ascending Kleene chain of f.
*)

Lemma omegaChain :
  forall f n m,
  monotone f ->
  leq (approx f n) (approx f m) \/ leq (approx f m) (approx f n).
Proof.
  intros.
  fact (natDiff n m).
  destruct H0; destruct H0.
  - right.
    rewrite H0; clear H0.
    generalize x.
    induction m; intros.
    + cbn; apply bottomLeast.
    + specialize (IHm x0); apply H in IHm.
      cbn; auto.
  - left.
    rewrite H0; clear H0.
    generalize x.
    induction n; intros.
    + cbn; apply bottomLeast.
    + specialize (IHn x0); apply H in IHn.
      cbn; auto.
Qed.

(* The ascending Kleene chain of f is directed. *)

Lemma kleeneChainDirected :
  forall f,
  monotone f ->
  directed (fun x2 => exists n, x2 = approx f n).
Proof.
  intros.
  set (P := fun x2 : T => exists n : nat, x2 = approx f n).
  unfold directed.
  split.
  - exists bottom; unfold P; exists 0; auto.
  - intros.
    unfold P in H0; destruct H0.
    unfold P in H1; destruct H1.
    fact (omegaChain f x x0 H).
    destruct H2.
    + exists x2.
      split.
      * rewrite H0; rewrite H1; auto.
      * {
        split.
        - apply refl.
        - unfold P.
          exists x0; auto.
      }
    + exists x1.
      split.
      * apply refl.
      * {
        split.
        - rewrite H0; rewrite H1; auto.
        - unfold P.
          exists x; auto.
      }
Qed.

(**********************************)
(* The Kleene fixed-point theorem *)
(**********************************)

(*
  The Kleene fixed-point theorem states that the least fixed-point of a Scott-
  continuous function over a pointed directed-complete partial order exists and
  is the supremum of the ascending Kleene chain.
*)

Theorem kleene :
  forall f,
  continuous f ->
  exists x1,
  supremum (fun x2 => exists n, x2 = approx f n) x1 /\
  f x1 = x1 /\
  (forall x2, f x2 = x2 -> leq x1 x2).
Proof.
  intros.
  set (P := fun x2 : T => exists n : nat, x2 = approx f n).
  assert (directed P).
  - apply kleeneChainDirected; apply continuousImpliesMonotone in H; auto.
  - fact (directedComplete P H0); destruct H1.
    exists x.
    split; auto.
    split.
    + unfold continuous in H.
      specialize (H P x H0 H1).
      set (Q := fun x2 : T => exists x3 : T, P x3 /\ x2 = f x3) in H.
      assert (supremum P (f x)).
      * {
        unfold supremum.
        split; intros.
        - unfold supremum in H; destruct H.
          unfold P in H2; destruct H2.
          destruct x0.
          + cbn in H2; rewrite H2; apply bottomLeast.
          + assert (Q x2).
            * {
              unfold Q.
              exists (approx f x0).
              split.
              - unfold P.
                exists x0; auto.
              - cbn in H2; auto.
            }
            * apply H; auto.
        - unfold supremum in H; destruct H.
          apply H3.
          intros.
          apply H2.
          unfold P.
          unfold Q in H4; destruct H4; destruct H4.
          unfold P in H4; destruct H4.
          rewrite H4 in H5.
          exists (S x1).
          cbn; auto.
      }
      * apply (supremumUniqueness P); auto.
    + intros.
      assert (forall x3, P x3 -> leq x3 x2).
      * {
        intros.
        unfold P in H3; destruct H3.
        generalize dependent x3.
        induction x0; intros.
        - cbn in H3; rewrite H3; apply bottomLeast.
        - specialize (IHx0 (approx f x0)); feed IHx0; auto.
          rewrite H3; clear H3.
          cbn.
          rewrite <- H2.
          fact (continuousImpliesMonotone f H).
          apply H3; auto.
      }
      * {
        unfold supremum in H1; destruct H1.
        apply H4; auto.
      }
Qed.

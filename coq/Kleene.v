(*******************************************************)
(*******************************************************)
(****                                               ****)
(****   A proof of the Kleene fixed-point theorem   ****)
(****                                               ****)
(*******************************************************)
(*******************************************************)

Require Import Main.Tactics.

Module Type Kleene.

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

  Hint Resolve refl.
  Hint Resolve trans.
  Hint Resolve antisym.

  (*
    A supremum of a subset of T is a least element of T which is greater than
    or equal to every element in the subset. This is also called a join or
    least upper bound.
  *)

  Definition supremum P x1 :=
    (forall x2, P x2 -> leq x2 x1) /\
    forall x3, (forall x2, P x2 -> leq x2 x3) -> leq x1 x3.

  (*
    A directed subset of T is a non-empty subset of T such that any two
    elements in the subset have an upper bound in the subset.
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

  Hint Resolve directedComplete.

  (*
    Assumption: Let T have a least element called bottom. This makes our
    partial order a pointed directed-complete partial order.
  *)

  Parameter bottom : T.

  Axiom bottomLeast : forall x, leq bottom x.

  Hint Resolve bottomLeast.

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
    identical and have the same order relation, but this need not be the case
    for continuous functions in general.
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

  (******************)
  (* Helpful lemmas *)
  (******************)

  (* We will need this simple lemma about pairs of natural numbers. *)

  Lemma natDiff : forall n1 n2, exists n3, n1 = n2 + n3 \/ n2 = n1 + n3.
  Proof.
    induction n1; intros.
    - exists n2. magic.
    - specialize (IHn1 n2). destruct IHn1. destruct H.
      + exists (S x). magic.
      + destruct x; [exists 1 | exists x]; magic.
  Qed.

  Hint Resolve natDiff.

  (* The supremum of a subset of T, if it exists, is unique. *)

  Lemma supremumUniqueness :
    forall P x1 x2,
    supremum P x1 ->
    supremum P x2 ->
    x1 = x2.
  Proof.
    unfold supremum.
    magic.
  Qed.

  Hint Resolve supremumUniqueness.

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
      + exists x1. magic.
      + intros.
        destruct H1; subst x0; exists x2; split; magic.
    - feed H.
      + unfold supremum.
        split.
        * intros. destruct H1; subst x0; magic.
        * magic.
      + unfold supremum in H. destruct H. specialize (H (f x1)). feed H.
        exists x1. magic.
  Qed.

  Hint Resolve continuousImpliesMonotone.

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
    intros. fact (natDiff n m). destruct H0. destruct H0.
    - right. subst n. induction m; magic.
    - left. subst m. induction n; magic.
  Qed.

  Hint Resolve omegaChain.

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
    - exists bottom. unfold P. exists 0. magic.
    - intros.
      unfold P in H0. destruct H0.
      unfold P in H1. destruct H1.
      fact (omegaChain f x x0 H).
      destruct H2.
      + exists x2.
        repeat (split; magic).
        unfold P. exists x0. magic.
      + exists x1.
        repeat (split; magic).
        unfold P. exists x. magic.
  Qed.

  Hint Resolve kleeneChainDirected.

  (**********************************)
  (* The Kleene fixed-point theorem *)
  (**********************************)

  (*
    The Kleene fixed-point theorem states that the least fixed-point of a
    Scott-continuous function over a pointed directed-complete partial order
    exists and is the supremum of the ascending Kleene chain.
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
    pose (P := fun x2 : T => exists n : nat, x2 = approx f n).
    assert (directed P).
    - apply kleeneChainDirected. apply continuousImpliesMonotone in H. magic.
    - fact (directedComplete P H0). destruct H1. exists x. split; magic. split.
      + unfold continuous in H.
        specialize (H P x H0 H1).
        set (Q := fun x2 : T => exists x3 : T, P x3 /\ x2 = f x3) in H.
        assert (supremum P (f x)).
        * {
          unfold supremum. split; intros.
          - unfold supremum in H. destruct H.
            unfold P in H2. destruct H2.
            destruct x0.
            + cbn in H2. subst x2. magic.
            + assert (Q x2); magic.
              unfold Q. exists (approx f x0).
              split; magic.
              unfold P. exists x0. magic.
          - unfold supremum in H. destruct H.
            apply H3.
            intros.
            apply H2.
            unfold P.
            unfold Q in H4. do 2 (destruct H4).
            unfold P in H4. destruct H4.
            exists (S x1).
            magic.
        }
        * apply (supremumUniqueness P); magic.
      + intros.
        assert (forall x3, P x3 -> leq x3 x2).
        * {
          intros.
          unfold P in H3. destruct H3.
          generalize dependent x3.
          induction x0; intros.
          - cbn in H3. subst x3. magic.
          - specialize (IHx0 (approx f x0)). feed IHx0.
            subst x3.
            cbn.
            rewrite <- H2.
            fact (continuousImpliesMonotone f H).
            magic.
        }
        * unfold supremum in H1. magic.
  Qed.

  Hint Resolve kleene.

End Kleene.

(*******************************************************)
(*******************************************************)
(****                                               ****)
(****   A proof of the Kleene fixed-point theorem   ****)
(****                                               ****)
(*******************************************************)
(*******************************************************)

Require Import Lia.
Require Import Main.Tactics.

Section Kleene.

  (***************)
  (* Definitions *)
  (***************)

  (*
    Assumption: Let (T, leq) be a partially ordered set, or poset. A poset is
    a set with a binary relation which is reflexive, transitive, and
    antisymmetric.
  *)

  Variable T : Type.
  Variable leq : T -> T -> Prop.

  Hypothesis refl : forall x, leq x x.
  Hypothesis trans : forall x y z, leq x y -> leq y z -> leq x z.
  Hypothesis antisym : forall x y, leq x y -> leq y x -> x = y.

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

  Hypothesis directedComplete :
    forall P,
    directed P ->
    exists x, supremum P x.

  (*
    Assumption: Let T have a least element called bottom. This makes our
    partial order a pointed directed-complete partial order.
  *)

  Variable bottom : T.

  Hypothesis bottomLeast : forall x, leq bottom x.

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

  #[local] Theorem natDiff :
    forall n1 n2,
    exists n3,
    n1 = n2 + n3 \/ n2 = n1 + n3.
  Proof.
    clean. induction n1; eMagic. clean.
    destruct H.
    - exists (S x). lia.
    - destruct x; [exists 1 | exists x]; lia.
  Qed.

  (* The supremum of a subset of T, if it exists, is unique. *)

  Theorem supremumUniqueness :
    forall P x1 x2,
    supremum P x1 ->
    supremum P x2 ->
    x1 = x2.
  Proof.
    unfold supremum. magic.
  Qed.

  (* Scott-continuity implies monotonicity. *)

  Theorem continuousImpliesMonotone : forall f, continuous f -> monotone f.
  Proof.
    unfold continuous. unfold monotone. clean.
    specialize (H (fun x => x = x1 \/ x = x2) x2). feed H.
    - unfold directed in H. split; eMagic.
    - unfold supremum in H. feed H; eMagic.
  Qed.

  (*
    Iterated applications of a monotone function f to bottom form an ω-chain,
    which means they are a totally ordered subset of T. This ω-chain is called
    the ascending Kleene chain of f.
  *)

  Theorem omegaChain :
    forall f n m,
    monotone f ->
    leq (approx f n) (approx f m) \/ leq (approx f m) (approx f n).
  Proof.
    clean. fact (natDiff n m). clean. destruct H0.
    - right. clean. induction m; magic.
    - left. clean. induction n; magic.
  Qed.

  (* The ascending Kleene chain of f is directed. *)

  Theorem kleeneChainDirected :
    forall f,
    monotone f ->
    directed (fun x2 => exists n, x2 = approx f n).
  Proof.
    clean.
    pose (P := fun x2 : T => exists n : nat, x2 = approx f n).
    unfold directed.
    split; clean.
    - exists bottom. exists 0. magic.
    - fact (omegaChain f x x0 H). destruct H0.
      + exists (approx f x0). eMagic.
      + exists (approx f x). eMagic.
  Qed.

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
    clean.
    pose (P := fun x2 : T => exists n : nat, x2 = approx f n).
    assert (directed P).
    - apply kleeneChainDirected. apply continuousImpliesMonotone in H. magic.
    - fact (directedComplete P H0). clean. exists x. split; magic. split.
      + unfold continuous in H.
        specialize (H P x H0 H1).
        set (Q := fun x2 : T => exists x3 : T, P x3 /\ x2 = f x3) in H.
        assert (supremum P (f x)).
        * {
          unfold supremum. split; unfold supremum in H; clean.
          - unfold P in H2. clean.
            destruct x0; magic.
            assert (Q (approx f (S x0))); magic.
            unfold Q. exists (approx f x0).
            split; magic.
            unfold P. eMagic.
          - apply H3. clean.
            apply H2. unfold P.
            unfold Q in H4. unfold P in H4. clean.
            exists (S x1). magic.
        }
        * apply (supremumUniqueness P); magic.
      + clean. assert (forall x3, P x3 -> leq x3 x2); clean.
        * unfold P in H3. clean.
          induction x0; magic.
          clean. rewrite <- H2.
          fact (continuousImpliesMonotone f H). magic.
        * unfold supremum in H1. magic.
  Qed.

End Kleene.

#[export] Hint Resolve supremumUniqueness : main.

#[export] Hint Resolve continuousImpliesMonotone : main.

#[export] Hint Resolve omegaChain : main.

#[export] Hint Resolve kleeneChainDirected : main.

#[export] Hint Resolve kleene : main.

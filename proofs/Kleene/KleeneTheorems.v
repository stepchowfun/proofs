(*******************************************************)
(*******************************************************)
(****                                               ****)
(****   A proof of the Kleene fixed-point theorem   ****)
(****                                               ****)
(*******************************************************)
(*******************************************************)

Require Import Coq.micromega.Lia.
Require Import Main.Kleene.KleeneData.
Require Import Main.Tactics.

Module KleeneTheorems (Kleene : KleeneData).
  Import Kleene.

  (***************)
  (* Definitions *)
  (***************)

  (*
    A monotone function is one which preserves order. We only need to consider
    functions for which the domain and codomain are identical and have the same
    order relation, but this need not be the case for monotone functions in
    general.
  *)

  Definition monotone f := forall x1 x2, leq x1 x2 -> leq (f x1) (f x2).

  #[export] Hint Unfold monotone : main.

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

  #[export] Hint Unfold continuous : main.

  (* This function performs iterated application of a function to `bottom`. *)

  Fixpoint approx f n :=
    match n with
    | 0 => bottom
    | S n => f (approx f n)
    end.

  (******************)
  (* Helpful lemmas *)
  (******************)

  (* We'll need this simple lemma about pairs of natural numbers. *)

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

  #[local] Hint Resolve natDiff : main.

  (* The supremum of a subset of `T`, if it exists, is unique. *)

  Theorem supremumUniqueness :
    forall P x1 x2,
    supremum P x1 ->
    supremum P x2 ->
    x1 = x2.
  Proof.
    unfold supremum. magic.
  Qed.

  #[export] Hint Resolve supremumUniqueness : main.

  (* Scott-continuity implies monotonicity. *)

  Theorem continuousImpliesMonotone : forall f, continuous f -> monotone f.
  Proof.
    unfold continuous. unfold monotone. clean.
    specialize (H (fun x => x = x1 \/ x = x2) x2). feed H.
    - unfold directed in H. split; eMagic.
    - unfold supremum in H. feed H; eMagic.
  Qed.

  #[export] Hint Resolve continuousImpliesMonotone : main.

  (*
    Iterated applications of a monotone function `f` to bottom form an
    ω-chain, which means they are a totally ordered subset of `T`. This
    ω-chain is called the ascending Kleene chain of `f`.
  *)

  Theorem omegaChain :
    forall f n m,
    monotone f ->
    leq (approx f n) (approx f m) \/ leq (approx f m) (approx f n).
  Proof.
    clean. pose proof (natDiff n m). clean. destruct H0.
    - right. clean. induction m; magic.
    - left. clean. induction n; magic.
  Qed.

  #[export] Hint Resolve omegaChain : main.

  (* The ascending Kleene chain of `f` is directed. *)

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
    - pose proof (omegaChain f x x0 H). destruct H0.
      + exists (approx f x0). eMagic.
      + exists (approx f x). eMagic.
  Qed.

  #[export] Hint Resolve kleeneChainDirected : main.

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
    - pose proof (directedComplete P H0). clean. exists x. split; magic. split.
      + unfold continuous in H.
        specialize (H P x H0 H1).
        set (Q := fun x2 : T => exists x3 : T, P x3 /\ x2 = f x3) in H.
        assert (supremum P (f x)).
        * unfold supremum. split; unfold supremum in H; clean.
          -- unfold P in H2. clean.
             destruct x0; magic.
             assert (Q (approx f (S x0))); magic.
             unfold Q. exists (approx f x0).
             split; magic.
             unfold P. eMagic.
          -- apply H3. clean.
             apply H2. unfold P.
             unfold Q in H4. unfold P in H4. clean.
             exists (S x1). magic.
        * apply (supremumUniqueness P); magic.
      + clean. assert (forall x3, P x3 -> leq x3 x2); clean.
        * unfold P in H3. clean.
          induction x0; magic.
          clean. rewrite <- H2.
          pose proof (continuousImpliesMonotone f H). magic.
        * unfold supremum in H1. magic.
  Qed.

  #[export] Hint Resolve kleene : main.
End KleeneTheorems.

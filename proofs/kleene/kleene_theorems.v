(*******************************************************)
(*******************************************************)
(****                                               ****)
(****   A proof of the Kleene fixed-point theorem   ****)
(****                                               ****)
(*******************************************************)
(*******************************************************)

Require Import Coq.micromega.Lia.
Require Import main.kleene.kleene_data.
Require Import main.tactics.

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

  Definition Monotone f := forall x1 x2, Leq x1 x2 -> Leq (f x1) (f x2).

  Hint Unfold Monotone : main.

  (*
    A function is Scott-continuous if it preserves suprema of directed subsets.
    We only need to consider functions for which the domain and codomain are
    identical and have the same order relation, but this need not be the case
    for continuous functions in general.
  *)

  Definition Continuous (f : T -> T) :=
    forall P x1,
    Directed P ->
    Supremum P x1 ->
    Supremum (fun x2 => exists x3, P x3 /\ x2 = f x3) (f x1).

  Hint Unfold Continuous : main.

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

  #[local] Theorem nat_diff :
    forall n1 n2,
    exists n3,
    n1 = n2 + n3 \/ n2 = n1 + n3.
  Proof.
    clean. induction n1; esearch. clean.
    destruct H.
    - exists (S x). lia.
    - destruct x; [exists 1 | exists x]; lia.
  Qed.

  #[local] Hint Resolve nat_diff : main.

  (* The supremum of a subset of `T`, if it exists, is unique. *)

  Theorem supremum_uniqueness :
    forall P x1 x2,
    Supremum P x1 ->
    Supremum P x2 ->
    x1 = x2.
  Proof.
    unfold Supremum. search.
  Qed.

  Hint Resolve supremum_uniqueness : main.

  (* Scott-continuity implies monotonicity. *)

  Theorem continuous_implis_monotone : forall f, Continuous f -> Monotone f.
  Proof.
    unfold Continuous. unfold Monotone. clean.
    specialize (H (fun x => x = x1 \/ x = x2) x2). feed H.
    - unfold Directed in H. split; esearch.
    - unfold Supremum in H. feed H; esearch.
  Qed.

  Hint Resolve continuous_implis_monotone : main.

  (*
    Iterated applications of a monotone function `f` to bottom form an
    ω-chain, which means they are a totally ordered subset of `T`. This
    ω-chain is called the ascending Kleene chain of `f`.
  *)

  Theorem omega_chain :
    forall f n m,
    Monotone f ->
    Leq (approx f n) (approx f m) \/ Leq (approx f m) (approx f n).
  Proof.
    clean. pose proof (nat_diff n m). clean. destruct H0.
    - right. clean. induction m; search.
    - left. clean. induction n; search.
  Qed.

  Hint Resolve omega_chain : main.

  (* The ascending Kleene chain of `f` is directed. *)

  Theorem kleene_chain_directed :
    forall f,
    Monotone f ->
    Directed (fun x2 => exists n, x2 = approx f n).
  Proof.
    clean.
    pose (P := fun x2 : T => exists n : nat, x2 = approx f n).
    unfold Directed.
    split; clean.
    - exists bottom. exists 0. search.
    - pose proof (omega_chain f x x0 H). destruct H0.
      + exists (approx f x0). esearch.
      + exists (approx f x). esearch.
  Qed.

  Hint Resolve kleene_chain_directed : main.

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
    Continuous f ->
    exists x1,
    Supremum (fun x2 => exists n, x2 = approx f n) x1 /\
    f x1 = x1 /\
    (forall x2, f x2 = x2 -> Leq x1 x2).
  Proof.
    clean.
    pose (P := fun x2 : T => exists n : nat, x2 = approx f n).
    assert (Directed P).
    - apply kleene_chain_directed.
      apply continuous_implis_monotone in H.
      search.
    - pose proof (directed_complete P H0).
      clean.
      exists x.
      split; search.
      split.
      + unfold Continuous in H.
        specialize (H P x H0 H1).
        set (Q := fun x2 : T => exists x3 : T, P x3 /\ x2 = f x3) in H.
        assert (Supremum P (f x)).
        * unfold Supremum. split; unfold Supremum in H; clean.
          -- unfold P in H2. clean.
             destruct x0; search.
             assert (Q (approx f (S x0))); search.
             unfold Q. exists (approx f x0).
             split; search.
             unfold P. esearch.
          -- apply H3. clean.
             apply H2. unfold P.
             unfold Q in H4. unfold P in H4. clean.
             exists (S x1). search.
        * apply (supremum_uniqueness P); search.
      + clean. assert (forall x3, P x3 -> Leq x3 x2); clean.
        * unfold P in H3. clean.
          induction x0; search.
          clean. rewrite <- H2.
          pose proof (continuous_implis_monotone f H). search.
        * unfold Supremum in H1. search.
  Qed.

  Hint Resolve kleene : main.
End KleeneTheorems.

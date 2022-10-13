(****************************************************************************)
(****************************************************************************)
(****                                                                    ****)
(****   A proof of the correctness of the simplest and most surprising   ****)
(****   sorting algorithm ever                                           ****)
(****                                                                    ****)
(****************************************************************************)
(****************************************************************************)

(*
  The "I can't believe it can sort" algorithm verified below comes from [1].

  [1] Stanley P. Y. Fung (2021). Is this the simplest (and most surprising)
      sorting algorithm ever? https://doi.org/10.48550/arXiv.2110.01111

*)

Require Import Coq.Arith.Compare_dec.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import Main.Tactics.

Import Coq.Init.Nat.
Import Coq.Lists.List.ListNotations.
Import PeanoNat.Nat.

(*****************)
(* The algorithm *)
(*****************)

Definition program := list nat -> list nat.

Definition update i x : program := fun l =>
  firstn i l ++ x :: skipn (S i) l.

Definition swap i j : program := fun l =>
  update j (nth i l 0) (update i (nth j l 0) l).

Definition compareAndSwap i j : program := fun l =>
  if nth i l 0 <? nth j l 0
  then swap i j l
  else l.

Definition forLoop body : program := fun l =>
  (
    fix recursiveForLoop n :=
      match n with
      | O => l
      | S p => body p (recursiveForLoop p)
      end
  ) (length l).

Definition sort : program :=
  forLoop (fun i =>
    forLoop (fun j =>
      compareAndSwap i j
    )
  ).

(**************)
(* Unit tests *)
(**************)

Goal sort [] = [].
Proof.
  search.
Qed.

Goal sort [3] = [3].
Proof.
  search.
Qed.

Goal sort [4; 3] = [3; 4].
Proof.
  search.
Qed.

Goal sort [3; 2; 4; 1; 5] = [1; 2; 3; 4; 5].
Proof.
  search.
Qed.

(*************************)
(* The correctness proof *)
(*************************)

(* Miscellaneous facts that could be in the standard library *)

Theorem sortedFirstn :
  forall A (l : list A) (R : A -> A -> Prop) n,
  Sorted R l ->
  Sorted R (firstn n l).
Proof.
  intros.
  outro n.
  induction l; search; intros; destruct n; search.
  invert H.
  clean.
  apply Sorted_cons; search.
  destruct H3, n; search.
Qed.

#[local] Hint Resolve sortedFirstn : core.

Theorem sortedSkipn :
  forall A (l : list A) (R : A -> A -> Prop) n,
  Sorted R l ->
  Sorted R (skipn n l).
Proof.
  intros.
  outro n.
  induction l; intros; destruct n; search.
  invert H.
  search.
Qed.

#[local] Hint Resolve sortedSkipn : core.

Theorem sortedApp :
  forall A (l1 l2 : list A) (x : A) (R : A -> A -> Prop),
  Sorted R l1 ->
  Sorted R l2 ->
  Forall (fun y => R y x) l1 ->
  HdRel R x l2 ->
  Sorted R (l1 ++ x :: l2).
Proof.
  intros.
  induction l1; search.
  cbn.
  apply Sorted_cons.
  - apply IHl1; [invert H | invert H1]; search.
  - invert H.
    destruct l1.
    + invert H1.
      search.
    + cbn.
      apply HdRel_cons.
      invert H6.
      search.
Qed.

#[local] Hint Resolve sortedApp : core.

Theorem nthFirstn :
  forall A d i j (l : list A),
  i < j ->
  nth i (firstn j l) d = nth i l d.
Proof.
  intros.
  outro i j.
  induction l; search; intros.
  - destruct j; search.
  - destruct i; destruct j; search.
    apply IHl; search.
Qed.

#[local] Hint Resolve nthFirstn : main.

Theorem consFirstnNth :
  forall A d i (l : list A),
  i < length l ->
  firstn i l ++ [nth i l d] = firstn (S i) l.
Proof.
  intros.
  outro i.
  induction l; intros; destruct i; search.
  change (firstn (S i) (a :: l) ++ [nth (S i) (a :: l) d])
    with (a :: firstn i l ++ [nth i l d]).
  rewrite IHl; search.
Qed.

#[local] Hint Resolve consFirstnNth : main.

Theorem nthSkipn :
  forall A d i j (l : list A), nth i (skipn j l) d = nth (i + j) l d.
Proof.
  intros.
  outro j.
  induction l; intros; destruct j; search.
  - replace (i + 0) with i; search.
  - replace (i + S j) with (S (i + j)); search.
Qed.

#[local] Hint Resolve nthSkipn : main.

Theorem skipnSkipn :
  forall A x y (l : list A),
  skipn x (skipn y l) =
  skipn (x + y) l.
Proof.
  intros.
  generalize x y.
  induction l; intros.
  - repeat rewrite skipn_nil.
    search.
  - destruct x0; destruct y0; search.
    replace (S x0 + S y0) with (S (S (x0 + y0))); search.
    repeat rewrite skipn_cons.
    rewrite IHl.
    search.
Qed.

#[local] Hint Resolve skipnSkipn : core.

(* Facts about `update` *)

Theorem nthUpdateSame :
  forall i x l,
  i < length l ->
  nth i (update i x l) 0 = x.
Proof.
  intros.
  unfold update.
  set (l0 := firstn i l).
  assert (length l0 = i).
  - apply firstn_length_le.
    search.
  - generalize (skipn (S i) l).
    intros.
    replace i with (length l0 + 0); search.
    apply app_nth2_plus.
Qed.

#[local] Hint Resolve nthUpdateSame : main.

Theorem nthUpdateOther :
  forall i j x l,
  j < length l ->
  i <> j ->
  nth i (update j x l) 0 = nth i l 0.
Proof.
  intros.
  destruct (lt_eq_lt_dec i j); [destruct s | idtac]; search.
  - unfold update.
    generalize (x :: skipn (S j) l).
    intros.
    replace (nth i (firstn j l ++ l1) 0) with (nth i (firstn j l) 0).
    + apply nthFirstn; search.
    + symmetry.
      apply app_nth1.
      replace (length (firstn j l)) with j; search.
      symmetry.
      apply firstn_length_le.
      search.
  - unfold update.
    assert (exists k, i = length (firstn j l) + k).
    + rewrite (firstn_length j l).
      rewrite min_l; search.
      induction i; search.
      destruct (lt_eq_lt_dec j i); [destruct s | idtac]; search.
      * repeat feed IHi.
        destruct IHi.
        exists (S x0).
        search.
      * rewrite e.
        exists 1.
        search.
    + destruct H1.
      replace (nth i (firstn j l ++ x :: skipn (S j) l) 0)
        with (
          nth (length (firstn j l) + x0) (firstn j l ++ x :: skipn (S j) l) 0
        ); search.
      rewrite app_nth2_plus.
      destruct x0.
      * assert (length (firstn j l) = j); search.
        apply firstn_length_le; search.
      * change (nth (S x0) (x :: skipn (S j) l) 0)
          with (nth x0 (skipn (S j) l) 0).
        rewrite nthSkipn.
        assert (length (firstn j l) = j); search.
        apply firstn_length_le; search.
Qed.

#[local] Hint Resolve nthUpdateOther : main.

Theorem updatePreservesLength :
  forall i x l,
  i < length l ->
  length (update i x l) = length l.
Proof.
  intros.
  unfold update.
  assert (length (firstn i l) = i).
  - apply firstn_length_le.
    search.
  - rewrite app_length.
    rewrite H0.
    change (length (x :: skipn (S i) l)) with (S (length (skipn (S i) l))).
    rewrite skipn_length.
    search.
Qed.

#[local] Hint Resolve updatePreservesLength : main.

(* Facts about `swap` *)

Theorem nthSwapLeft :
  forall i j l,
  i < length l ->
  j < length l ->
  nth i (swap i j l) 0 = nth j l 0.
Proof.
  intros.
  unfold swap.
  destruct (eq_dec i j).
  - rewrite e.
    rewrite nthUpdateSame; search.
    rewrite updatePreservesLength; search.
  - rewrite nthUpdateOther; search.
    rewrite updatePreservesLength; search.
Qed.

#[local] Hint Resolve nthSwapLeft : main.

Theorem nthSwapRight :
  forall i j l,
  i < length l ->
  j < length l ->
  nth j (swap i j l) 0 = nth i l 0.
Proof.
  intros.
  unfold swap.
  destruct (eq_dec i j);
    [rewrite e | idtac];
    rewrite nthUpdateSame;
    search;
    rewrite updatePreservesLength;
    search.
Qed.

#[local] Hint Resolve nthSwapRight : main.

Theorem nthSwapOther :
  forall i j k l,
  i < length l ->
  j < length l ->
  k <> i ->
  k <> j ->
  nth k (swap i j l) 0 = nth k l 0.
Proof.
  intros.
  unfold swap.
  rewrite nthUpdateOther; search.
  rewrite updatePreservesLength; search.
Qed.

#[local] Hint Resolve nthSwapOther : main.

Theorem swapPreservesLength :
  forall i j l,
  i < length l ->
  j < length l ->
  length (swap i j l) = length l.
Proof.
  intros.
  unfold swap.
  replace (length l) with (length (update i (nth j l 0) l)) in *; search.
Qed.

#[local] Hint Resolve swapPreservesLength : main.

Theorem swapPermutes :
  forall i j l,
  i < length l ->
  j < length l ->
  Permutation l (swap i j l).
Proof.
  intros.
  apply <- Permutation_nth.
  split.
  - unfold swap.
    repeat rewrite updatePreservesLength; search.
  - exists (fun k => if k =? i then j else if k =? j then i else k).
    split.
    + unfold FinFun.bFun.
      search.
    + unfold FinFun.bInjective.
      split; intros.
      * destruct (eq_dec x i);
        destruct (eq_dec x j);
        destruct (eq_dec y i);
        destruct (eq_dec y j);
        pose proof (eqb_neq x i);
        pose proof (eqb_neq x j);
        pose proof (eqb_neq y i);
        pose proof (eqb_neq y j);
        search.
      * destruct (eq_dec x i);
        destruct (eq_dec x j);
        pose proof (eqb_neq x i);
        pose proof (eqb_neq x j);
        search.
Qed.

#[local] Hint Resolve swapPermutes : main.

(* Facts about `compareAndSwap` *)

Theorem compareAndSwapPreservesLength :
  forall i j l,
  i < length l ->
  j < length l ->
  length (compareAndSwap i j l) = length l.
Proof.
  unfold compareAndSwap.
  search.
Qed.

#[local] Hint Resolve compareAndSwapPreservesLength : main.

Theorem compareAndSwapPermutes :
  forall i j l,
  i < length l ->
  j < length l ->
  Permutation l (compareAndSwap i j l).
Proof.
  unfold compareAndSwap.
  search.
Qed.

#[local] Hint Resolve compareAndSwapPermutes : main.

(* Facts about `forLoop` *)

Theorem forLoopInduction :
  forall (P : nat -> list nat -> Prop) body l1,
  P 0 l1 ->
  (forall n2 l2, n2 < length l1 -> P n2 l2 -> P (S n2) (body n2 l2)) ->
  P (length l1) (forLoop body l1).
Proof.
  intros.
  set (n1 := length l1).
  assert (n1 <= length l1); search.
  unfold forLoop.
  change (length l1) with n1.
  induction n1; search.
  apply H0; search.
  apply IHn1; search.
Qed.

(* Facts about `sort` *)

Theorem sortPreservesLength : forall l, length (sort l) = length l.
Proof.
  intros.
  unfold sort.
  pose proof forLoopInduction (fun _ l2 => length l2 = length l).
  apply H; search.
  intros i ? ? ?.
  apply H; search.
  intros j ? ? ?.
  rewrite <- H3.
  apply compareAndSwapPreservesLength; search.
Qed.

#[local] Hint Resolve sortPreservesLength : main.

Theorem sortPermutes : forall l, Permutation l (sort l).
Proof.
  intros.
  unfold sort.
  pose proof forLoopInduction (fun _ l2 => Permutation l l2).
  apply H; search.
  intros i ? ? ?.
  apply H; search.
  intros j ? ? ?.
  rewrite Permutation_length with (l' := l0) in H0; search.
  rewrite Permutation_length with (l' := l0) in H2; search.
  - apply Permutation_trans with (l' := l0); search.
  - apply Permutation_trans with (l' := l); search.
    apply Permutation_sym.
    search.
Qed.

#[local] Hint Resolve sortPermutes : main.

Theorem sortOrders : forall l, Sorted le (sort l).
Proof.
  intros.
  rewrite <- firstn_all.
  rewrite sortPreservesLength.
  set (n := length l).
  cut (
    let sorted := sort l in
    Sorted le (firstn (length l) sorted) /\
    length sorted = n
  ); search.
  cbv zeta.
  unfold sort.
  apply forLoopInduction; search.
  subst n.
  intros i ? ? ?.
  destruct H0.
  rewrite <- H1 in *.
  clear H1 l.
  split.
  - set (n := length l2).
    cut (
      let state := forLoop (fun j : nat => compareAndSwap i j) l2 in
      Sorted le (firstn i state) /\
      (forall n1, n1 < length l2 -> nth n1 state 0 <= nth i state 0) /\
      length state = n
    ); cbv zeta.
    + generalize dependent (forLoop (fun j : nat => compareAndSwap i j) l2).
      intros.
      destruct H1.
      destruct H2.
      rewrite <- consFirstnNth with (d := 0); search.
      apply sortedApp; search.
      apply Forall_nth.
      intros.
      rewrite firstn_length in H4.
      rewrite nthFirstn; search.
      rewrite nth_indep with (d := d) (d' := 0); search.
      apply H2.
      search.
    + apply forLoopInduction; [idtac | intros j ? ? ?]; repeat split; search.
      * destruct H2, H3.
        unfold compareAndSwap.
        set (iv := nth i l0 0).
        set (jv := nth j l0 0).
        destruct (lt_dec iv jv).
        -- replace (iv <? jv) with true.
           ++ destruct (le_lt_dec i j).
              ** replace (firstn i (swap i j l0)) with (firstn i l0); search.
                 apply nth_ext with (d := 0) (d' := 0).
                 --- repeat rewrite firstn_length; search.
                     rewrite swapPreservesLength; search.
                 --- intros.
                     rewrite firstn_length in H5.
                     repeat rewrite nthFirstn; search.
                     rewrite nthSwapOther; search.
              ** rewrite <- (firstn_skipn j).
                 replace (firstn j (firstn i (swap i j l0)))
                   with (firstn j (swap i j l0)).
                 --- replace (firstn j (swap i j l0)) with (firstn j l0).
                     +++ replace (skipn j (firstn i (swap i j l0)))
                           with (nth i l0 0 :: skipn (S j) (firstn i l0)).
                         *** apply sortedApp; search.
                             ---- replace (firstn j l0)
                                    with (firstn j (firstn i l0)); search.
                                  rewrite firstn_firstn.
                                  search.
                             ---- apply Forall_nth.
                                  intros.
                                  rewrite firstn_length in H5.
                                  rewrite nthFirstn; search.
                                  rewrite nth_indep with (d := d) (d' := 0);
                                    search.
                                  apply H3.
                                  search.
                             ---- change (S j) with (1 + j).
                                  rewrite <- skipnSkipn.
                                  assert (Sorted le (skipn j (firstn i l0)));
                                    search.
                                  invert H5; search.
                                  cbn.
                                  assert (a = jv).
                                  ++++ change a with (nth 0 (a :: l3) 0).
                                       rewrite H6.
                                       rewrite nthSkipn.
                                       rewrite nthFirstn; search.
                                  ++++ destruct H8; search.
                                       apply HdRel_cons; search.
                         *** apply nth_ext with (d := 0) (d' := 0).
                             ---- change (
                                    S (length (skipn (S j) (firstn i l0))) =
                                    length (skipn j (firstn i (swap i j l0)))
                                  ).
                                  repeat rewrite skipn_length.
                                  repeat rewrite firstn_length.
                                  rewrite swapPreservesLength; search.
                             ---- intros.
                                  change (
                                    n0 < S (length (skipn (S j) (firstn i l0)))
                                  ) in H5.
                                  rewrite skipn_length in H5.
                                  rewrite firstn_length in H5.
                                  replace (Nat.min i (length l0)) with i in H5;
                                    search.
                                  rewrite nthSkipn.
                                  rewrite nthFirstn; search.
                                  destruct n0.
                                  ++++ rewrite nthSwapRight; search.
                                  ++++ rewrite nthSwapOther; search.
                                       change (
                                         nth n0 (skipn (S j) (firstn i l0)) 0 =
                                           nth (S n0 + j) l0 0
                                       ).
                                       rewrite nthSkipn.
                                       rewrite nthFirstn; search.
                     +++ apply nth_ext with (d := 0) (d' := 0).
                         *** repeat rewrite firstn_length.
                             rewrite swapPreservesLength; search.
                         *** intros.
                             rewrite firstn_length in H5.
                             repeat rewrite nthFirstn; search.
                             rewrite nthSwapOther; search.
                 --- rewrite firstn_firstn.
                     search.
           ++ symmetry.
              apply (ltb_lt iv jv).
              search.
        -- replace (iv <? jv) with false; search.
           symmetry.
           apply (ltb_ge iv jv).
           search.
      * intros.
        destruct H2, H4.
        unfold compareAndSwap.
        set (iv := nth i l0 0).
        set (jv := nth j l0 0).
        destruct (lt_dec iv jv).
        -- replace (iv <? jv) with true.
           ++ destruct (lt_eq_lt_dec n1 j); [destruct s | idtac]; search.
              ** destruct (eq_dec n1 i); search.
                 rewrite nthSwapLeft; search.
                 rewrite nthSwapOther; search.
                 specialize (H4 n1).
                 search.
              ** rewrite e.
                 rewrite nthSwapRight; search.
                 rewrite nthSwapLeft; search.
           ++ symmetry.
              apply (ltb_lt iv jv).
              search.
        -- replace (iv <? jv) with false.
           ++ destruct (lt_eq_lt_dec n1 j); [destruct s | idtac]; search.
           ++ symmetry.
              apply (ltb_ge iv jv).
              search.
      * rewrite compareAndSwapPreservesLength; search.
  - apply (forLoopInduction (fun _ l3 => length l3 = length l2)); search.
    intros.
    rewrite <- H2.
    apply compareAndSwapPreservesLength; search.
Qed.

#[local] Hint Resolve sortOrders : main.

Theorem sortCorrect : forall l, Permutation l (sort l) /\ Sorted le (sort l).
Proof.
  search.
Qed.

#[local] Hint Resolve sortCorrect : main.

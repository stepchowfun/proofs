(*******************************************)
(*******************************************)
(****                                   ****)
(****   "I can't believe it can sort"   ****)
(****                                   ****)
(*******************************************)
(*******************************************)

(*
  This file proves the correctness of the simple and surprising *I can't
  believe it can sort* algorithm [1]:

  for 0 <= i < n
    for 0 <= j < n
      if a[i] < a[j]
        swap a[i] and a[j]

  [1] Stanley P. Y. Fung (2021). Is this the simplest (and most surprising)
      sorting algorithm ever? https://doi.org/10.48550/arXiv.2110.01111
*)

Require Import Coq.Arith.Compare_dec.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorted.
Require Import main.tactics.

Import Coq.Arith.PeanoNat.Nat.
Import Coq.Lists.List.ListNotations.

(*****************)
(* The algorithm *)
(*****************)

Definition program := list nat -> list nat.

Definition update i x : program := fun l =>
  firstn i l ++ x :: skipn (S i) l.

Definition swap i j : program := fun l =>
  update j (nth i l 0) (update i (nth j l 0) l).

Definition compare_and_swap i j : program := fun l =>
  if nth i l 0 <? nth j l 0
  then swap i j l
  else l.

Definition for_loop body : program := fun l =>
  (
    fix recursive_for_loop n :=
      match n with
      | O => l
      | S p => body p (recursive_for_loop p)
      end
  ) (length l).

Definition sort : program :=
  for_loop (fun i =>
    for_loop (fun j =>
      compare_and_swap i j
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

(* Miscellaneous facts that could be added to the standard library *)

Theorem sorted_firstn :
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

#[local] Hint Resolve sorted_firstn : core.

Theorem sorted_skipn :
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

#[local] Hint Resolve sorted_skipn : core.

Theorem sorted_app :
  forall A (x : A) l1 l2 (R : A -> A -> Prop),
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

#[local] Hint Resolve sorted_app : core.

Theorem nth_firstn :
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

#[local] Hint Resolve nth_firstn : main.

Theorem cons_firstn_nth :
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

#[local] Hint Resolve cons_firstn_nth : main.

Theorem nth_skipn :
  forall A d i j (l : list A), nth i (skipn j l) d = nth (i + j) l d.
Proof.
  intros.
  outro j.
  induction l; intros; destruct j; search.
  - replace (i + 0) with i; search.
  - replace (i + S j) with (S (i + j)); search.
Qed.

#[local] Hint Resolve nth_skipn : main.

Theorem skipn_skipn :
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

#[local] Hint Resolve skipn_skipn : core.

(* Facts about `update` *)

Theorem nth_update_same :
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

#[local] Hint Resolve nth_update_same : main.

Theorem nth_update_other :
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
    + apply nth_firstn; search.
    + symmetry.
      apply app_nth1.
      replace (length (firstn j l)) with j; search.
      symmetry.
      apply firstn_length_le.
      search.
  - unfold update.
    assert (exists k, i = length (firstn j l) + k).
    + rewrite (length_firstn j l).
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
        rewrite nth_skipn.
        assert (length (firstn j l) = j); search.
        apply firstn_length_le; search.
Qed.

#[local] Hint Resolve nth_update_other : main.

Theorem update_preserves_length :
  forall i x l,
  i < length l ->
  length (update i x l) = length l.
Proof.
  intros.
  unfold update.
  assert (length (firstn i l) = i).
  - apply firstn_length_le.
    search.
  - rewrite length_app.
    rewrite H0.
    change (length (x :: skipn (S i) l)) with (S (length (skipn (S i) l))).
    rewrite length_skipn.
    search.
Qed.

#[local] Hint Resolve update_preserves_length : main.

(* Facts about `swap` *)

Theorem nth_swap_left :
  forall i j l,
  i < length l ->
  j < length l ->
  nth i (swap i j l) 0 = nth j l 0.
Proof.
  intros.
  unfold swap.
  destruct (eq_dec i j).
  - rewrite e.
    rewrite nth_update_same; search.
    rewrite update_preserves_length; search.
  - rewrite nth_update_other; search.
    rewrite update_preserves_length; search.
Qed.

#[local] Hint Resolve nth_swap_left : main.

Theorem nth_swap_right :
  forall i j l,
  i < length l ->
  j < length l ->
  nth j (swap i j l) 0 = nth i l 0.
Proof.
  intros.
  unfold swap.
  destruct (eq_dec i j);
    [rewrite e | idtac];
    rewrite nth_update_same;
    search;
    rewrite update_preserves_length;
    search.
Qed.

#[local] Hint Resolve nth_swap_right : main.

Theorem nth_swap_other :
  forall i j k l,
  i < length l ->
  j < length l ->
  k <> i ->
  k <> j ->
  nth k (swap i j l) 0 = nth k l 0.
Proof.
  intros.
  unfold swap.
  rewrite nth_update_other; search.
  rewrite update_preserves_length; search.
Qed.

#[local] Hint Resolve nth_swap_other : main.

Theorem swap_preserves_length :
  forall i j l,
  i < length l ->
  j < length l ->
  length (swap i j l) = length l.
Proof.
  intros.
  unfold swap.
  replace (length l) with (length (update i (nth j l 0) l)) in *; search.
Qed.

#[local] Hint Resolve swap_preserves_length : main.

Theorem swap_permutes :
  forall i j l,
  i < length l ->
  j < length l ->
  Permutation l (swap i j l).
Proof.
  intros.
  apply <- Permutation_nth.
  split.
  - unfold swap.
    repeat rewrite update_preserves_length; search.
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

#[local] Hint Resolve swap_permutes : main.

(* Facts about `compare_and_swap` *)

Theorem compare_and_swap_preserves_length :
  forall i j l,
  i < length l ->
  j < length l ->
  length (compare_and_swap i j l) = length l.
Proof.
  unfold compare_and_swap.
  search.
Qed.

#[local] Hint Resolve compare_and_swap_preserves_length : main.

Theorem compare_and_swap_permutes :
  forall i j l,
  i < length l ->
  j < length l ->
  Permutation l (compare_and_swap i j l).
Proof.
  unfold compare_and_swap.
  search.
Qed.

#[local] Hint Resolve compare_and_swap_permutes : main.

(* Facts about `for_loop` *)

Theorem for_loop_induction :
  forall (P : nat -> list nat -> Prop) body l1,
  P 0 l1 ->
  (forall n2 l2, n2 < length l1 -> P n2 l2 -> P (S n2) (body n2 l2)) ->
  P (length l1) (for_loop body l1).
Proof.
  intros.
  set (n1 := length l1).
  assert (n1 <= length l1); search.
  unfold for_loop.
  change (length l1) with n1.
  induction n1; search.
  apply H0; search.
  apply IHn1; search.
Qed.

(* Facts about `sort` *)

Theorem sort_inner_loop_preserves_length :
  forall l i,
  i < length l ->
  length (for_loop (fun j : nat => compare_and_swap i j) l) = length l.
Proof.
  intros.
  apply (for_loop_induction (fun _ l3 => length l3 = length l)); search.
  intros.
  rewrite <- H1.
  apply compare_and_swap_preserves_length; search.
Qed.

#[local] Hint Resolve sort_inner_loop_preserves_length : main.

Theorem sort_preserves_length : forall l, length (sort l) = length l.
Proof.
  intros.
  apply (for_loop_induction (fun _ l2 => length l2 = length l)); search.
  intros.
  rewrite <- H0 in *.
  search.
Qed.

#[local] Hint Resolve sort_preserves_length : main.

Theorem sort_permutes : forall l, Permutation l (sort l).
Proof.
  intros.
  unfold sort.
  pose proof for_loop_induction (fun _ l2 => Permutation l l2).
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

#[local] Hint Resolve sort_permutes : main.

Theorem sort_compare_and_swap_preserves_sorted_prefix :
  forall i j l,
  i < length l ->
  j < length l ->
  (forall k : nat, k < j -> nth k l 0 <= nth i l 0) ->
  Sorted le (firstn i l) ->
  Sorted le (firstn i (compare_and_swap i j l)).
Proof.
  intros.
  unfold compare_and_swap.
  set (iv := nth i l 0).
  set (jv := nth j l 0).
  destruct (lt_dec iv jv).
  - replace (iv <? jv) with true.
    + destruct (le_lt_dec i j).
      * replace (firstn i (swap i j l)) with (firstn i l); search.
        apply nth_ext with (d := 0) (d' := 0).
        -- repeat rewrite length_firstn; search.
           rewrite swap_preserves_length; search.
        -- intros.
           rewrite length_firstn in H3.
           repeat rewrite nth_firstn; search.
           rewrite nth_swap_other; search.
      * rewrite <- (firstn_skipn j).
        replace (firstn j (firstn i (swap i j l)))
          with (firstn j (swap i j l)).
        -- replace (firstn j (swap i j l)) with (firstn j l).
           ++ replace (skipn j (firstn i (swap i j l)))
                with (nth i l 0 :: skipn (S j) (firstn i l)).
              ** apply sorted_app; search.
                 --- replace (firstn j l)
                       with (firstn j (firstn i l)); search.
                     rewrite firstn_firstn.
                     search.
                 --- apply Forall_nth.
                     intros.
                     rewrite length_firstn in H3.
                     rewrite nth_firstn; search.
                     rewrite nth_indep with (d := d) (d' := 0);
                     search.
                     apply H1.
                     search.
                 --- change (S j) with (1 + j).
                     rewrite <- skipn_skipn.
                     assert (Sorted le (skipn j (firstn i l)));
                     search.
                     invert H3; search.
                     cbn.
                     assert (a = jv).
                     +++ change a with (nth 0 (a :: l2) 0).
                         rewrite H4.
                         rewrite nth_skipn.
                         rewrite nth_firstn; search.
                     +++ destruct H6; search.
              ** apply nth_ext with (d := 0) (d' := 0).
                 --- change (
                       S (length (skipn (S j) (firstn i l))) =
                       length (skipn j (firstn i (swap i j l)))
                     ).
                     repeat rewrite length_skipn.
                     repeat rewrite length_firstn.
                     rewrite swap_preserves_length; search.
                 --- intros.
                     change (
                       n < S (length (skipn (S j) (firstn i l)))
                     ) in H3.
                     rewrite length_skipn in H3.
                     rewrite length_firstn in H3.
                     replace (Nat.min i (length l)) with i in H3;
                     search.
                     rewrite nth_skipn.
                     rewrite nth_firstn; search.
                     destruct n.
                     +++ rewrite nth_swap_right; search.
                     +++ rewrite nth_swap_other; search.
                         change (
                           nth n (skipn (S j) (firstn i l)) 0 =
                           nth (S n + j) l 0
                         ).
                         rewrite nth_skipn.
                         rewrite nth_firstn; search.
           ++ apply nth_ext with (d := 0) (d' := 0).
              ** repeat rewrite length_firstn.
                 rewrite swap_preserves_length; search.
              ** intros.
                 rewrite length_firstn in H3.
                 repeat rewrite nth_firstn; search.
                 rewrite nth_swap_other; search.
        -- rewrite firstn_firstn.
           search.
    + symmetry.
      apply (ltb_lt iv jv).
      search.
  - replace (iv <? jv) with false; search.
    symmetry.
    apply (ltb_ge iv jv).
    search.
Qed.

#[local] Hint Resolve sort_compare_and_swap_preserves_sorted_prefix : main.

Theorem sort_compare_and_swap_advances_maximized_prefix :
  forall i j k l,
  i < length l ->
  j < length l ->
  k <= j ->
  (forall h : nat, h < j -> nth h l 0 <= nth i l 0) ->
  nth k (compare_and_swap i j l) 0 <= nth i (compare_and_swap i j l) 0.
Proof.
  intros.
  unfold compare_and_swap.
  set (iv := nth i l 0).
  set (jv := nth j l 0).
  destruct (lt_dec iv jv).
  - replace (iv <? jv) with true.
    + destruct (lt_eq_lt_dec k j); [destruct s | idtac]; search.
      * destruct (eq_dec k i); search.
        rewrite nth_swap_left; search.
        rewrite nth_swap_other; search.
        specialize (H2 k).
        search.
      * rewrite e.
        rewrite nth_swap_right; search.
        rewrite nth_swap_left; search.
    + symmetry.
      apply (ltb_lt iv jv).
      search.
  - replace (iv <? jv) with false.
    + destruct (lt_eq_lt_dec k j); [destruct s | idtac]; search.
    + symmetry.
      apply (ltb_ge iv jv).
      search.
Qed.

#[local] Hint Resolve sort_compare_and_swap_advances_maximized_prefix : main.

Theorem sort_inner_loop_advances_sorted_prefix :
  forall i l,
  i < length l ->
  Sorted le (firstn i l) ->
  Sorted le (firstn (S i) (for_loop (fun j : nat => compare_and_swap i j) l)).
Proof.
  intros.
  remember (length l).
  cut (
    let state := for_loop (fun j : nat => compare_and_swap i j) l in
    Sorted le (firstn i state) /\
    (forall k, k < length l -> nth k state 0 <= nth i state 0) /\
    length state = n
  ); cbv zeta.
  + generalize dependent (for_loop (fun j : nat => compare_and_swap i j) l).
    intros.
    destruct H1.
    destruct H2.
    rewrite <- cons_firstn_nth with (d := 0); search.
    apply sorted_app; search.
    apply Forall_nth.
    intros.
    rewrite length_firstn in H4.
    rewrite nth_firstn; search.
    rewrite nth_indep with (d := d) (d' := 0); search.
    apply H2.
    search.
  + apply for_loop_induction; [idtac | intros j ? ? ?]; repeat split; search.
    * apply sort_compare_and_swap_preserves_sorted_prefix; search.
    * intros.
      apply sort_compare_and_swap_advances_maximized_prefix; search.
    * rewrite compare_and_swap_preserves_length; search.
Qed.

#[local] Hint Resolve sort_inner_loop_advances_sorted_prefix : main.

Theorem sort_orders : forall l, Sorted le (sort l).
Proof.
  intros.
  rewrite <- firstn_all.
  rewrite sort_preserves_length.
  remember (length l).
  cut (
    let sorted := sort l in
    Sorted le (firstn (length l) sorted) /\
    length sorted = n
  ); search.
  cbv zeta.
  unfold sort.
  apply for_loop_induction; search.
  subst n.
  intros i ? ? ?.
  destruct H0.
  rewrite <- H1 in *.
  split; search.
Qed.

#[local] Hint Resolve sort_orders : main.

Theorem sort_correct : forall l, Permutation l (sort l) /\ Sorted le (sort l).
Proof.
  search.
Qed.

#[local] Hint Resolve sort_correct : main.

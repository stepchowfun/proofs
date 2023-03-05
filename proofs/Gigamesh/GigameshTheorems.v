(***************************************)
(***************************************)
(****                               ****)
(****   Theorems about gigameshes   ****)
(****                               ****)
(***************************************)
(***************************************)

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import Main.Gigamesh.Gigamesh.
Require Import Main.Tactics.

Module GigameshTheorems (Graph : Gigamesh).
  Import Graph.

  #[local] Arguments clos_refl_trans {A} _ _ _.
  #[local] Arguments clos_refl_trans_1n {A} _ _ _.
  #[local] Arguments clos_refl_trans_n1 {A} _ _ _.
  #[local] Hint Constructors clos_refl_trans : main.
  #[local] Hint Constructors clos_refl_trans_1n : main.
  #[local] Hint Constructors clos_refl_trans_n1 : main.
  #[local] Hint Resolve clos_rt1n_rt : main.
  #[local] Hint Resolve clos_rt_rt1n : main.
  #[local] Hint Resolve clos_rtn1_rt : main.
  #[local] Hint Resolve clos_rt_rtn1 : main.

  (*
    *Reachability* is the reflexive transitive closure of the edge relation.
  *)

  Definition reachable := clos_refl_trans edge.

  #[export] Hint Unfold reachable : main.

  (* The root is its own parent. *)

  Theorem rootParent : parent root = root.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve rootParent : main.
  #[export] Hint Rewrite rootParent : main.

  (* The root is the only node which is its own parent. *)

  Theorem selfParent : forall n, n = parent n -> n = root.
  Proof.
    clean.
    induction (rootedness n); search.
  Qed.

  #[export] Hint Resolve selfParent : main.

  (* The root is the only node which is an ancestor of the root. *)

  Theorem ancestorOfRoot : forall n, ancestor n root -> n = root.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve ancestorOfRoot : main.

  (* The ancestors of a given node are totally ordered. *)

  Theorem ancestorsTotallyOrdered :
    forall n1 n2 n3,
    ancestor n1 n3 ->
    ancestor n2 n3 ->
    ancestor n1 n2 \/
    ancestor n2 n1.
  Proof.
    clean.
    assert (clos_refl_trans_n1 (fun n1 n2 => n1 = parent n2) n1 n3); search.
    induction H1; search.
    assert (clos_refl_trans_n1 (fun n1 n2 => n1 = parent n2) n2 z); search.
    destruct H3; search.
  Qed.

  #[export] Hint Resolve ancestorsTotallyOrdered : main.

  (* Parenthood implies reachability. *)

  Theorem parentReach : forall n, reachable (parent n) n.
  Proof.
    clean.
    remember (parent n).
    apply clos_rtn1_rt.
    assert (
      clos_refl_trans_n1 (fun n1 n2 : node =>
        edge n1 n2 /\ ancestor n0 n2
      ) n0 n
    ); search.
    clear Heqn0.
    induction H; eSearch.
  Qed.

  #[export] Hint Resolve parentReach : main.

  (* Ancestorship implies reachability. *)

  Theorem ancestorReach : forall n1 n2, ancestor n1 n2 -> reachable n1 n2.
  Proof.
    clean.
    induction H; eSearch.
    clean.
    search.
  Qed.

  #[export] Hint Resolve ancestorReach : main.
End GigameshTheorems.

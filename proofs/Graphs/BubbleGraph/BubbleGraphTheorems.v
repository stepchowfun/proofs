(******************************************)
(******************************************)
(****                                  ****)
(****   Theorems about bubble graphs   ****)
(****                                  ****)
(******************************************)
(******************************************)

Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.
Require Import Main.Graphs.BubbleGraph.BubbleGraph.
Require Import Main.Tactics.

Module BubbleGraphTheorems (Graph : BubbleGraph).
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
    If a node is a member of a bubble, the node is reachable from the root of
    the bubble.
  *)

  Theorem memberReach :
    forall b n, member b n -> clos_refl_trans edge (root b) n.
  Proof.
    clean.
    assert (
      clos_refl_trans_n1 (
        fun n1 n2 : node => edge n1 n2 /\ member b n2
      ) (root b) n
    ); search.
    clear H.
    induction H0; eSearch.
  Qed.

  #[export] Hint Resolve memberReach : main.
End BubbleGraphTheorems.

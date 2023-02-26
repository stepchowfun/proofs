(************************************************)
(************************************************)
(****                                        ****)
(****   Theorems about causal cover graphs   ****)
(****                                        ****)
(************************************************)
(************************************************)

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import Main.Graphs.CausalCoverGraph.CausalCoverGraph.
Require Import Main.Tactics.

Module CausalCoverGraphTheorems (Graph : CausalCoverGraph).
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
    If an event is a member of its own causal cover, then the cover contains
    only that event.
  *)

  Theorem endocover : forall e1 e2, cover e1 e2 -> cover e2 e2 -> e1 = e2.
  Proof.
    eSearch.
  Qed.

  #[export] Hint Resolve endocover : main.
End CausalCoverGraphTheorems.

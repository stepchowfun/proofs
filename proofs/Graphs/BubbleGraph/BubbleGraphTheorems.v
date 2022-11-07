(******************************************)
(******************************************)
(****                                  ****)
(****   Theorems about bubble graphs   ****)
(****                                  ****)
(******************************************)
(******************************************)

Require Import Coq.Relations.Relation_Operators.
Require Import Main.Graphs.BubbleGraph.BubbleGraph.
Require Import Main.Tactics.

Module BubbleGraphTheorems (Graph : BubbleGraph).
  Import Graph.

  #[local] Arguments clos_refl_trans {A} _ _ _.
  #[local] Hint Constructors clos_refl_trans : main.

  (* Every node is reachable from the root of the universe. *)

  Theorem rootReach : forall n, clos_refl_trans edge (root universe) n.
  Proof.
    clean.
    induction (connectedness universe n); search.
    apply rt_trans with (y := y); search.
  Qed.

  #[export] Hint Resolve rootReach : main.
End BubbleGraphTheorems.

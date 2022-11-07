(************************************************)
(************************************************)
(****                                        ****)
(****   The simplest possible bubble graph   ****)
(****                                        ****)
(************************************************)
(************************************************)

Require Import Coq.Relations.Relation_Operators.
Require Import Main.Graphs.BubbleGraph.BubbleGraph.
Require Import Main.Graphs.BubbleGraph.BubbleGraphTheorems.
Require Import Main.Tactics.

Module TrivialBubbleGraph <: BubbleGraph.
  #[local] Arguments clos_refl_trans {A} _ _ _.
  #[local] Hint Resolve rt_refl : main.

  Definition node := unit.

  Definition edge (n1 n2 : node) := False.

  Definition bubble := unit.

  Definition root (b : bubble) := tt.

  Definition member (b : bubble) (n : node) := True.

  Theorem connectedness :
    forall b n,
    member b n ->
    clos_refl_trans (fun n1 n2 => edge n1 n2 /\ member b n2) (root b) n.
  Proof.
    clean.
    destruct n.
    search.
  Qed.

  #[export] Hint Resolve connectedness : main.

  Definition universe := tt.

  Theorem universality : forall n, member universe n.
  Proof.
    unfold member.
    search.
  Qed.

  #[export] Hint Resolve universality : main.
End TrivialBubbleGraph.

Module TrivialBubbleGraphTheorems := BubbleGraphTheorems TrivialBubbleGraph.

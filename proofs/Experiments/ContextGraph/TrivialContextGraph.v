(*************************************************)
(*************************************************)
(****                                         ****)
(****   The simplest possible context graph   ****)
(****                                         ****)
(*************************************************)
(*************************************************)

Require Import Coq.Relations.Relation_Operators.
Require Import Main.Experiments.ContextGraph.ContextGraph.
Require Import Main.Experiments.ContextGraph.ContextGraphTheorems.
Require Import Main.Tactics.

Module TrivialContextGraph <: ContextGraph.
  #[local] Arguments clos_refl_trans {A} _ _ _.
  #[local] Hint Resolve rt_refl : main.

  Definition node := unit.

  #[export] Hint Unfold node : main.

  Definition edge (c n1 n2 : node) := False.

  #[export] Hint Unfold edge : main.

  (* Coq requires that we copy this verbatim from `ContextGraph`. *)
  Definition horizontallyReachable c := clos_refl_trans (edge c).

  #[export] Hint Unfold horizontallyReachable : main.

  (* Coq requires that we copy this verbatim from `ContextGraph`. *)
  Definition contextualizes c := horizontallyReachable c c.

  #[export] Hint Unfold contextualizes : main.

  (* Coq requires that we copy this verbatim from `ContextGraph`. *)
  Definition verticallyReachable := clos_refl_trans contextualizes.

  #[export] Hint Unfold verticallyReachable : main.

  Theorem contextualSoundness :
    forall c n1 n2,
    edge c n1 n2 ->
    contextualizes c n1.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve contextualSoundness : main.

  Theorem verticalAntisymmetry :
    forall n1 n2,
    verticallyReachable n1 n2 ->
    verticallyReachable n2 n1 ->
    n1 = n2.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve verticalAntisymmetry : main.

  Definition root := tt.

  #[export] Hint Unfold root : main.

  Theorem rootReach : forall n, verticallyReachable root n.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve rootReach : main.
End TrivialContextGraph.

Module TrivialContextGraphTheorems := ContextGraphTheorems TrivialContextGraph.

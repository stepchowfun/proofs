(*************************************************)
(*************************************************)
(****                                         ****)
(****   The simplest possible context graph   ****)
(****                                         ****)
(*************************************************)
(*************************************************)

Require Import Coq.Relations.Relation_Operators.
Require Import Main.ContextGraph.ContextGraph.
Require Import Main.Tactics.

Module TrivialContextGraph <: ContextGraph.
  #[local] Arguments clos_refl_trans {A} _ _ _.

  Definition node := unit.

  Definition edge (x y z : node) := False.

  (* Coq requires that we copy this verbatim from `ContextGraph`. *)
  Definition horizontallyReachable c := clos_refl_trans (edge c).

  (* Coq requires that we copy this verbatim from `ContextGraph`. *)
  Definition rooted c := horizontallyReachable c c.

  (* Coq requires that we copy this verbatim from `ContextGraph`. *)
  Definition verticallyReachable := clos_refl_trans rooted.

  Theorem verticalAntisymmetry :
    forall n1 n2,
    verticallyReachable n1 n2 ->
    verticallyReachable n2 n1 ->
    n1 = n2.
  Proof.
    clean.
    elim n1.
    elim n2.
    magic.
  Qed.

  Definition origin := tt.

  Theorem originality : forall n, verticallyReachable origin n.
  Proof.
    clean.
    elim origin.
    elim n.
    apply rt_refl.
  Qed.
End TrivialContextGraph.

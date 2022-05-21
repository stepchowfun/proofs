(*************************************************)
(*************************************************)
(****                                         ****)
(****   The simplest possible context graph   ****)
(****                                         ****)
(*************************************************)
(*************************************************)

Require Import Coq.Relations.Relation_Operators.
Require Import Main.Experiments.ContextGraph.ContextGraph.
Require Import Main.Tactics.

Module TrivialContextGraph <: ContextGraph.
  #[local] Arguments clos_refl_trans {A} _ _ _.

  Definition node := unit.

  #[export] Hint Unfold node : main.

  Definition edge (c n1 n2 : node) := False.

  #[export] Hint Unfold edge : main.

  (* Coq requires that we copy this verbatim from `ContextGraph`. *)
  Definition horizontallyReachable c := clos_refl_trans (edge c).

  #[export] Hint Unfold horizontallyReachable : main.

  (* Coq requires that we copy this verbatim from `ContextGraph`. *)
  Definition proxies c := horizontallyReachable c c.

  #[export] Hint Unfold proxies : main.

  (* Coq requires that we copy this verbatim from `ContextGraph`. *)
  Definition verticallyReachable := clos_refl_trans proxies.

  #[export] Hint Unfold verticallyReachable : main.

  Theorem verticalAntisymmetry :
    forall n1 n2,
    verticallyReachable n1 n2 ->
    verticallyReachable n2 n1 ->
    n1 = n2.
  Proof.
    clean.
    destruct n1.
    destruct n2.
    magic.
  Qed.

  #[export] Hint Resolve verticalAntisymmetry : main.

  Definition root := tt.

  #[export] Hint Unfold root : main.

  Theorem rootReach : forall n, verticallyReachable root n.
  Proof.
    clean.
    destruct n.
    apply rt_refl.
  Qed.

  #[export] Hint Resolve rootReach : main.
End TrivialContextGraph.

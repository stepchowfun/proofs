(********************************************)
(********************************************)
(****                                    ****)
(****   The simplest possible overtree   ****)
(****                                    ****)
(********************************************)
(********************************************)

Require Import Coq.Relations.Relation_Operators.
Require Import Main.Graphs.Overtree.Overtree.
Require Import Main.Graphs.Overtree.OvertreeTheorems.
Require Import Main.Tactics.

Module TrivialOvertree <: Overtree.
  #[local] Arguments clos_refl_trans {A} _ _ _.
  #[local] Hint Resolve rt_refl : main.

  Definition node := unit.

  Definition edge (n1 n2 : node) := False.

  Definition parent (n : node) := tt.

  Theorem connectedness :
    forall n,
    clos_refl_trans (
      fun n1 n2 => edge n1 n2 /\ parent n2 = parent n
    ) (parent n) n.
  Proof.
    unfold node.
    search.
  Qed.

  #[export] Hint Resolve connectedness : main.

  (* Coq requires that we copy this verbatim from `Overtree`. *)
  Definition ancestor := clos_refl_trans (fun n1 n2 => n1 = parent n2).

  #[export] Hint Unfold ancestor : main.

  Theorem ancestorAntisymmetry :
    forall n1 n2, ancestor n1 n2 -> ancestor n2 n1 -> n1 = n2.
  Proof.
    unfold node.
    search.
  Qed.

  #[export] Hint Resolve ancestorAntisymmetry : main.

  (* There is a *root* node which is an ancestor for every node. *)

  Definition root := tt.

  Theorem rootedness : forall n, ancestor root n.
  Proof.
    unfold node.
    search.
  Qed.

  #[export] Hint Resolve rootedness : main.
End TrivialOvertree.

Module TrivialOvertreeTheorems := OvertreeTheorems TrivialOvertree.

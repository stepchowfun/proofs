(*******************************************)
(*******************************************)
(****                                   ****)
(****   The simplest possible overdag   ****)
(****                                   ****)
(*******************************************)
(*******************************************)

Require Import Coq.Relations.Relation_Operators.
Require Import Main.Graphs.Overdag.Overdag.
Require Import Main.Graphs.Overdag.OverdagTheorems.
Require Import Main.Tactics.

Module TrivialOverdag <: Overdag.
  #[local] Arguments clos_refl_trans {A} _ _ _.
  #[local] Hint Resolve rt_refl : main.

  Definition node := unit.

  Definition edge (n1 n2 : node) := False.

  Definition parent (p : node) (n : node) := False.

  Theorem connectedness :
    forall p n,
    parent p n ->
    clos_refl_trans (fun n1 n2 => edge n1 n2 /\ parent p n2) p n.
  Proof.
    unfold node.
    search.
  Qed.

  #[export] Hint Resolve connectedness : main.

  (* Coq requires that we copy this verbatim from `Overdag`. *)
  Definition ancestor := clos_refl_trans parent.

  #[export] Hint Unfold ancestor : main.

  Theorem ancestorshipAntisymmetry :
    forall n1 n2, ancestor n1 n2 -> ancestor n2 n1 -> n1 = n2.
  Proof.
    unfold node.
    search.
  Qed.

  #[export] Hint Resolve ancestorshipAntisymmetry : main.

  (* There is a *root* node which is an ancestor for every node. *)

  Definition root := tt.

  Theorem rootedness : forall n, ancestor root n.
  Proof.
    unfold node.
    search.
  Qed.

  #[export] Hint Resolve rootedness : main.
End TrivialOverdag.

Module TrivialOverdagTheorems := OverdagTheorems TrivialOverdag.

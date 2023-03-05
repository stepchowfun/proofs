(********************************************)
(********************************************)
(****                                    ****)
(****   The simplest possible gigamesh   ****)
(****                                    ****)
(********************************************)
(********************************************)

Require Import Coq.Relations.Relation_Operators.
Require Import Main.Gigamesh.Gigamesh.
Require Import Main.Gigamesh.GigameshTheorems.
Require Import Main.Tactics.

Module TrivialGigamesh <: Gigamesh.
  #[local] Arguments clos_refl_trans {A} _ _ _.
  #[local] Hint Resolve rt_refl : main.

  Definition node := unit.

  #[export] Hint Unfold node : main.

  Definition root := tt.

  #[export] Hint Unfold root : main.

  Definition edge (n1 n2 : node) := False.

  #[export] Hint Unfold edge : main.

  Definition parent (p : node) (n : node) := True.

  #[export] Hint Unfold parent : main.

  (* Coq requires that we copy this verbatim from `Gigamesh`. *)
  Definition ancestor := clos_refl_trans parent.

  #[export] Hint Unfold ancestor : main.

  Theorem reflexivity : forall n, parent n n.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve reflexivity : main.

  Theorem connectedness :
    forall p n,
    parent p n ->
    clos_refl_trans (fun n1 n2 => edge n1 n2 /\ ancestor p n2) p n.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve connectedness : main.

  Theorem encapsulation :
    forall n1 n2, edge n1 n2 -> exists p, ancestor p n1 /\ parent p n2.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve encapsulation : main.

  Theorem antisymmetry :
    forall n1 n2, ancestor n1 n2 -> ancestor n2 n1 -> n1 = n2.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve antisymmetry : main.

  Theorem rootedness : forall n, ancestor root n.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve rootedness : main.
End TrivialGigamesh.

Module TrivialGigameshTheorems := GigameshTheorems TrivialGigamesh.

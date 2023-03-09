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

  Definition edge (n1 n2 : node) := False.

  #[export] Hint Unfold edge : main.

  Definition parent (n1 : node) (n2 : node) := False.

  #[export] Hint Unfold parent : main.

  (* Coq requires that we copy this verbatim from `Gigamesh`. *)
  Definition ancestor := clos_refl_trans parent.

  #[export] Hint Unfold ancestor : main.

  Theorem antisymmetry :
    forall n1 n2, ancestor n1 n2 -> ancestor n2 n1 -> n1 = n2.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve antisymmetry : main.

  (* Coq requires that we copy this verbatim from `Gigamesh`. *)
  Definition admitted n1 n2 :=
    exists n3 n4, ancestor n3 n1 /\ parent n3 n4 /\ ancestor n2 n4.

  #[export] Hint Unfold admitted : main.

  Theorem admission : forall n1 n2, edge n1 n2 -> admitted n1 n2.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve admission : main.
End TrivialGigamesh.

Module TrivialGigameshTheorems := GigameshTheorems TrivialGigamesh.

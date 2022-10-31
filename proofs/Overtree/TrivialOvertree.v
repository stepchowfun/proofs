(********************************************)
(********************************************)
(****                                    ****)
(****   The simplest possible overtree   ****)
(****                                    ****)
(********************************************)
(********************************************)

Require Import Coq.Relations.Relation_Operators.
Require Import Main.Overtree.Overtree.
Require Import Main.Overtree.OvertreeTheorems.
Require Import Main.Tactics.

Module TrivialOvertree <: Overtree.
  #[local] Arguments clos_refl_trans {A} _ _ _.
  #[local] Hint Resolve rt_refl : main.

  Definition node := unit.

  #[export] Hint Unfold node : main.

  Definition edge (n1 n2 : node) := True.

  #[export] Hint Unfold edge : main.

  Definition owner (n : node) := tt.

  #[export] Hint Unfold owner : main.

  (* Coq requires that we copy this verbatim from `Overtree`. *)
  Definition covalent n1 n2 := edge n1 n2 /\ owner n1 = owner n2.

  #[export] Hint Unfold covalent : main.

  (* Coq requires that we copy this verbatim from `Overtree`. *)
  Definition reachable := clos_refl_trans covalent.

  #[export] Hint Unfold reachable : main.

  (* Coq requires that we copy this verbatim from `Overtree`. *)
  Definition owns n1 n2 :=
    owner n2 = n1 /\
    exists n3,
    edge n1 n3 /\
    reachable n3 n2.

  #[export] Hint Unfold owns : main.

  (* Coq requires that we copy this verbatim from `Overtree`. *)
  Definition contains := clos_refl_trans owns.

  #[export] Hint Unfold contains : main.

  Definition root := tt.

  #[export] Hint Unfold root : main.

  Theorem rootSelfOwned : owns root root.
  Proof.
    eSearch.
  Qed.

  #[export] Hint Resolve rootSelfOwned : main.

  Theorem rootedness : forall n, contains root n.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve rootedness : main.
End TrivialOvertree.

Module TrivialOvertreeTheorems := OvertreeTheorems TrivialOvertree.

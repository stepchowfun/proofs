(********************************************)
(********************************************)
(****                                    ****)
(****   The simplest possible overtree   ****)
(****                                    ****)
(********************************************)
(********************************************)

Require Import Coq.Relations.Relation_Operators.
Require Import Main.Experiments.Overtree.Overtree.
Require Import Main.Experiments.Overtree.OvertreeTheorems.
Require Import Main.Tactics.

Module TrivialOvertree <: Overtree.
  #[local] Arguments clos_refl_trans {A} _ _ _.
  #[local] Hint Resolve rt_refl : main.

  Definition node := unit.

  #[export] Hint Unfold node : main.

  Definition edge (n1 n2 : node) := True.

  #[export] Hint Unfold edge : main.

  Definition proxy (n : node) := tt.

  #[export] Hint Unfold proxy : main.

  (* Coq requires that we copy this verbatim from `Overtree`. *)
  Definition covalent n1 n2 := edge n1 n2 /\ proxy n1 = proxy n2.

  #[export] Hint Unfold covalent : main.

  (* Coq requires that we copy this verbatim from `Overtree`. *)
  Definition horizontallyReachable := clos_refl_trans covalent.

  #[export] Hint Unfold horizontallyReachable : main.

  (* Coq requires that we copy this verbatim from `Overtree`. *)
  Definition proxies n1 n2 :=
    proxy n2 = n1 /\
    exists n3,
    edge n1 n3 /\
    horizontallyReachable n3 n2.

  #[export] Hint Unfold proxies : main.

  (* Coq requires that we copy this verbatim from `Overtree`. *)
  Definition verticallyReachable := clos_refl_trans proxies.

  #[export] Hint Unfold verticallyReachable : main.

  Definition root := tt.

  #[export] Hint Unfold root : main.

  Theorem rootLoop : edge root root.
  Proof.
    magic.
  Qed.

  #[export] Hint Resolve rootLoop : main.

  Theorem rootProxy : proxy root = root.
  Proof.
    magic.
  Qed.

  #[export] Hint Resolve rootProxy : main.
  #[export] Hint Rewrite rootProxy : main.

  Theorem rootReach : forall n, verticallyReachable root n.
  Proof.
    magic.
  Qed.

  #[export] Hint Resolve rootReach : main.
End TrivialOvertree.

Module TrivialOvertreeTheorems := OvertreeTheorems TrivialOvertree.

(********************************************)
(********************************************)
(****                                    ****)
(****   The simplest possible overtree   ****)
(****                                    ****)
(********************************************)
(********************************************)

Require Import Coq.Relations.Relation_Operators.
Require Import Main.Experiments.Overtree.Overtree.
Require Import Main.Tactics.

Module TrivialOvertree <: Overtree.
  #[local] Arguments clos_refl_trans {A} _ _ _.

  Definition node := unit.

  Definition edge (n1 n2 : node) := True.

  Definition proxy (n : node) := tt.

  (* Coq requires that we copy this verbatim from `Overtree`. *)
  Definition covalent n1 n2 := edge n1 n2 /\ proxy n1 = proxy n2.

  (* Coq requires that we copy this verbatim from `Overtree`. *)
  Definition horizontallyReachable := clos_refl_trans covalent.

  (* Coq requires that we copy this verbatim from `Overtree`. *)
  Definition proxies n1 n2 :=
    proxy n2 = n1 /\
    exists n3,
    edge n1 n3 /\
    horizontallyReachable n3 n2.

  (* Coq requires that we copy this verbatim from `Overtree`. *)
  Definition verticallyReachable := clos_refl_trans proxies.

  Definition root := tt.

  Theorem rootProxy : proxy root = root.
  Proof.
    magic.
  Qed.

  Theorem rootEdge : edge root root.
  Proof.
    apply I.
  Qed.

  Theorem rootReach : forall n, verticallyReachable root n.
  Proof.
    clean.
    destruct n.
    apply rt_refl.
  Qed.
End TrivialOvertree.

Module TrivialOvertreeTheorems := OvertreeTheorems TrivialOvertree.

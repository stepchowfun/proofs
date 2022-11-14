(*************************************)
(*************************************)
(****                             ****)
(****   Theorems about overdags   ****)
(****                             ****)
(*************************************)
(*************************************)

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Setoids.Setoid.
Require Import Main.Graphs.Overdag.Overdag.
Require Import Main.Tactics.

Module OverdagTheorems (Graph : Overdag).
  Import Graph.

  #[local] Arguments clos_refl_trans {A} _ _ _.
  #[local] Arguments clos_refl_trans_1n {A} _ _ _.
  #[local] Arguments clos_refl_trans_n1 {A} _ _ _.
  #[local] Hint Constructors clos_refl_trans : main.
  #[local] Hint Constructors clos_refl_trans_1n : main.
  #[local] Hint Constructors clos_refl_trans_n1 : main.
  #[local] Hint Resolve clos_rt1n_rt : main.
  #[local] Hint Resolve clos_rt_rt1n : main.
  #[local] Hint Resolve clos_rtn1_rt : main.
  #[local] Hint Resolve clos_rt_rtn1 : main.

  (* Ancestorship implies reachability. *)

  Theorem ancestorReach :
    forall n1 n2, ancestor n1 n2 -> clos_refl_trans edge n1 n2.
  Proof.
    clean.
    assert (clos_refl_trans_n1 member n1 n2); search.
    induction H0; search.
    apply rt_trans with (y := y); search.
    pose proof (connectedness y z H0).
    assert (
      clos_refl_trans_n1 (
        fun n1 n2 : node => edge n1 n2 /\ member y n2
      ) y z
    ); search.
    clear H H0 H1 H2 IHclos_refl_trans_n1 n1.
    induction H3; search.
    apply rt_trans with (y := y0); search.
  Qed.

  #[export] Hint Resolve ancestorReach : main.
End OverdagTheorems.

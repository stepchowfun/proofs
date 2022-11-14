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

  (* The only node that can have the root as a member is the root. *)

  Theorem rootMember : forall n, member n root -> n = root.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve rootMember : main.

  (* The root is the only node which is an ancestor of the root. *)

  Theorem ancestorOfRoot : forall n, ancestor n root -> n = root.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve ancestorOfRoot : main.

  (* Membership implies reachability. *)

  Theorem memberReach :
    forall n1 n2, member n1 n2 -> clos_refl_trans edge n1 n2.
  Proof.
    clean.
    pose proof (connectedness n1 n2 H).
    assert (
      clos_refl_trans_n1 (
        fun n2 n3 : node => edge n2 n3 /\ member n1 n3
      ) n1 n2
    ); search.
    clear H.
    induction H1; search.
    apply rt_trans with (y := y); search.
  Qed.

  #[export] Hint Resolve memberReach : main.

  (* Ancestorship implies reachability. *)

  Theorem ancestorReach :
    forall n1 n2, ancestor n1 n2 -> clos_refl_trans edge n1 n2.
  Proof.
    clean.
    assert (clos_refl_trans_n1 member n1 n2); search.
    induction H0; search.
    apply rt_trans with (y := y); search.
  Qed.

  #[export] Hint Resolve ancestorReach : main.
End OverdagTheorems.

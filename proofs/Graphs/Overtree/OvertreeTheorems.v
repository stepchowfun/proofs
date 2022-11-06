(**************************************)
(**************************************)
(****                              ****)
(****   Theorems about overtrees   ****)
(****                              ****)
(**************************************)
(**************************************)

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.
Require Import Main.Graphs.Overtree.Overtree.
Require Import Main.Tactics.

Module OvertreeTheorems (Graph : Overtree).
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

  (* The root is the only node which is its own owner. *)

  Theorem rootUniquelySelfOwned : forall n, owner n = n -> n = root.
  Proof.
    clean.
    induction (rootedness n); search.
  Qed.

  #[export] Hint Resolve rootUniquelySelfOwned : main.

  (* The root is the only node which contains itself. *)

  Theorem rootUniquelyContained : forall n, contains n root -> n = root.
  Proof.
    clean.
    assert (clos_refl_trans_n1 owns n root); search.
    pose proof rootOwner.
    induction H0; search.
    assert (y = z); search.
  Qed.

  #[export] Hint Resolve rootUniquelyContained : main.

  (* If a node is reachable from another node, they share an owner. *)

  Theorem covalency : forall n1 n2, reachable n1 n2 -> owner n1 = owner n2.
  Proof.
    clean.
    induction H; search.
  Qed.

  #[export] Hint Resolve covalency : main.

  (* The owner for a given node is unique. *)

  Theorem ownerUniqueness :
    forall n1 n2 n3,
    owns n1 n3 ->
    owns n2 n3 ->
    n1 = n2.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve ownerUniqueness : main.

  (* Every node is owned by its owner. *)

  Theorem soundness : forall n, owns (owner n) n.
  Proof.
    clean.
    assert (clos_refl_trans_n1 owns root n).
    - apply clos_rt_rtn1.
      apply rootedness.
    - invert H.
      + split; eSearch.
      + invert H0.
        search.
  Qed.

  #[export] Hint Resolve soundness : main.

  (* Every node must be contained by its owner. *)

  Theorem containment : forall n, contains (owner n) n.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve containment : main.

  (* Containment is antisymmetric and thus a partial order. *)

  Theorem containmentAntisymmetry :
    forall n1 n2,
    contains n1 n2 ->
    contains n2 n1 ->
    n1 = n2.
  Proof.
    clean.
    assert (n1 <> n2 -> contains n2 root).
    - assert (clos_refl_trans_1n owns root n1).
      + apply clos_rt_rt1n.
        apply rootedness.
      + induction H1; search.
        clean.
        assert (clos_refl_trans_n1 owns n2 y); search.
        destruct H4; eSearch.
        assert (clos_refl_trans_n1 owns z n2); search.
        destruct H4; eSearch.
    - destruct (classic (n1 = n2)); search.
      pose proof (rootUniquelyContained n2).
      search.
  Qed.

  #[export] Hint Resolve containmentAntisymmetry : main.

  (* The nodes which contain a given node are totally ordered. *)

  Theorem containersTotallyOrdered :
    forall n1 n2 n3,
    contains n1 n3 ->
    contains n2 n3 ->
    contains n1 n2 \/
    contains n2 n1.
  Proof.
    clean.
    assert (clos_refl_trans_n1 owns n1 n3); search.
    induction H1; search.
    assert (clos_refl_trans_n1 owns n2 z); search.
    destruct H3; search.
  Qed.

  #[export] Hint Resolve containersTotallyOrdered : main.
End OvertreeTheorems.

(**********************************)
(**********************************)
(****                          ****)
(****   Admissibility graphs   ****)
(****                          ****)
(**********************************)
(**********************************)

Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.
Require Import Main.Tactics.

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

(*
  The *nodes* of an *admissibility graph* are related by two types of directed
  edges: *trusts* and *exports*.
*)

Record admissibilityGraph (node : Type) := {
  trusts : node -> node -> Prop;
  exports : node -> node -> Prop;
}.

Arguments trusts {_} _ _.
Arguments exports {_} _ _.

(*
  Every node may depend on itself, the nodes it trusts, the nodes that export
  it, any node that a node that trusts it can depend on, and any node that is
  exported by a node that it can depend on.
*)

Inductive allowed {node} (g : admissibilityGraph node) (n : node) : node
  -> Prop :=
| loop : allowed g n n
| trust : forall n1, trusts g n n1 -> allowed g n n1
| export : forall n1, exports g n1 n -> allowed g n n1
| egress : forall n1 n2, trusts g n1 n -> allowed g n1 n2 -> allowed g n n2
| ingress : forall n1 n2, exports g n1 n2 -> allowed g n n1 -> allowed g n n2.

#[export] Hint Constructors allowed : main.

(* It doesn't matter if a node trusts or exports itself. *)

Theorem self :
  forall (node : Type) (g1 g2 : admissibilityGraph node),
  (forall n1 n2, n1 = n2 /\ (trusts g1 n1 n2 <-> trusts g2 n1 n2)) ->
  (forall n1 n2, n1 = n2 /\ (exports g1 n1 n2 <-> exports g2 n1 n2)) ->
  forall n1 n2, allowed g1 n1 n2 <-> allowed g2 n1 n2.
Proof.
  split; clean.
  - induction H1; search.
    + destruct (H n n1).
      eSearch.
    + destruct (H0 n1 n).
      eSearch.
    + destruct (H n1 n).
      eSearch.
    + destruct (H0 n1 n2).
      eSearch.
  - induction H1; search.
    + destruct (H n n1).
      eSearch.
    + destruct (H0 n1 n).
      eSearch.
    + destruct (H n1 n).
      eSearch.
    + destruct (H0 n1 n2).
      eSearch.
Qed.

#[export] Hint Resolve self : main.

(*
  The following theorem gives an equivalent way to characterize which
  dependencies should be allowed.
*)

Theorem admission :
  forall (node : Type) (g : admissibilityGraph node) n1 n2,
  allowed g n1 n2 <->
  exists n3 n4,
    clos_refl_trans (fun n5 n6 => trusts g n6 n5) n1 n3 /\
    (n3 = n4 \/ trusts g n3 n4 \/ exports g n4 n3) /\
    clos_refl_trans (fun n5 n6 => exports g n5 n6) n4 n2.
Proof.
  split; clean.
  - induction H.
    + exists n, n.
      search.
    + exists n, n1.
      search.
    + exists n, n1.
      search.
    + destruct IHallowed.
      destruct H1.
      exists x, x0.
      eSearch.
    + destruct IHallowed.
      destruct H1.
      exists x, x0.
      eSearch.
  - induction (clos_rt_rt1n node (fun n5 n6 => trusts g n6 n5) n1 x H);
    induction (clos_rt_rtn1 node (fun n5 n6 => exports g n5 n6) x0 n2 H1);
    eSearch.
Qed.

#[export] Hint Resolve admission : main.

(*
  Given two admissibility graphs with the same set of nodes such that edges in
  the first graph imply corresponding edges of the opposite type in the second
  graph, then the second graph allows flipped versions of any dependencies
  allowed by the first graph.
*)

Theorem duality :
  forall (node : Type) (g1 g2 : admissibilityGraph node),
  (forall n1 n2, trusts g1 n1 n2 -> exports g2 n1 n2) ->
  (forall n1 n2, exports g1 n1 n2 -> trusts g2 n1 n2) ->
  forall n1 n2, allowed g1 n1 n2 -> allowed g2 n2 n1.
Proof.
  clean.
  destruct (admission node g1 n1 n2).
  specialize (H2 H1).
  clear H1 H3.
  destruct H2.
  do 2 destruct H1.
  destruct H2.
  apply admission.
  exists x0, x.
  repeat split; search.
  - clear H H1 H2.
    apply clos_rt_rt1n in H3.
    induction H3; eSearch.
  - clear H0 H2 H3.
    apply clos_rt_rtn1 in H1.
    induction H1; eSearch.
Qed.

#[export] Hint Resolve duality : main.

(*
  Swapping the edge types in an admissibility graph results in flipping the
  direction of the allowed dependencies.
*)

Theorem transposition :
  forall (node : Type) (g1 g2 : admissibilityGraph node),
  (forall n1 n2, trusts g1 n1 n2 <-> exports g2 n1 n2) ->
  (forall n1 n2, exports g1 n1 n2 <-> trusts g2 n1 n2) ->
  forall n1 n2, allowed g1 n1 n2 <-> allowed g2 n2 n1.
Proof.
  split; apply duality.
  - apply H.
  - apply H0.
  - apply H0.
  - clean.
    apply <- H.
    search.
Qed.

#[export] Hint Resolve transposition : main.

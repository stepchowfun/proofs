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
  The *nodes* of an *admissibility graph* are related by a *membership*
  relation. Nodes may be *trusted*, *exported*, both, or neither.
*)

Record admissibilityGraph (node : Type) := {
  member : node -> node -> Prop;
  trusted : node -> Prop;
  exported : node -> Prop;
}.

Arguments member {_} _ _.
Arguments trusted {_} _.
Arguments exported {_} _.

(*
  Every node may depend on itself, its members, and the groups containing it.
  A trusted node may also depend on any node that any of the groups containing
  it may depend on. A node may also depend on any exported members of any nodes
  that it may depend on.
*)

Inductive allowed {node} (g : admissibilityGraph node) (n : node) : node
  -> Prop :=
| loop : allowed g n n
| leave : forall n1, member g n n1 -> allowed g n n1
| enter : forall n1, member g n1 n -> allowed g n n1
| egress :
  forall n1 n2,
  trusted g n ->
  member g n n1 ->
  allowed g n1 n2 ->
  allowed g n n2
| ingress :
  forall n1 n2,
  exported g n2 ->
  member g n2 n1 ->
  allowed g n n1 ->
  allowed g n n2.

#[export] Hint Constructors allowed : main.

(*
  The following theorem gives an equivalent way to characterize which
  dependencies should be allowed.
*)

Theorem admission :
  forall (node : Type) (g : admissibilityGraph node) n1 n2,
  allowed g n1 n2 <->
  exists n3 n4,
    clos_refl_trans (fun n5 n6 => member g n5 n6 /\ trusted g n5) n1 n3 /\
    (n3 = n4 \/ member g n3 n4 \/ member g n4 n3) /\
    clos_refl_trans (fun n5 n6 => member g n6 n5 /\ exported g n6) n4 n2.
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
      destruct H2.
      exists x, x0.
      eSearch.
    + destruct IHallowed.
      destruct H2.
      exists x, x0.
      eSearch.
  - induction (
      clos_rt_rt1n node (fun n5 n6 => member g n5 n6 /\ trusted g n5) n1 x H
    );
    induction (
      clos_rt_rtn1 node (fun n5 n6 => member g n6 n5 /\ exported g n6) x0 n2 H1
    );
    eSearch.
Qed.

#[export] Hint Resolve admission : main.

(*
  Given two admissibility graphs with the same nodes and edges such that
  trusted nodes in the first graph are exported in the second graph and
  exported nodes in the second graph are trusted in the second graph, the
  second graph allows flipped versions of any dependencies allowed by the first
  graph.
*)

Theorem duality :
  forall (node : Type) (g1 g2 : admissibilityGraph node),
  (forall n, trusted g1 n -> exported g2 n) ->
  (forall n, exported g1 n -> trusted g2 n) ->
  (forall n1 n2, member g1 n1 n2 -> member g2 n1 n2) ->
  forall n1 n2, allowed g1 n1 n2 -> allowed g2 n2 n1.
Proof.
  clean.
  apply admission.
  destruct (admission node g1 n1 n2).
  specialize (H3 H2).
  clear H2 H4.
  destruct H3.
  do 2 destruct H2.
  destruct H3.
  exists x0, x.
  repeat split; eSearch.
  - clear H H2 H3.
    induction H4; eSearch.
  - clear H0 H3 H4.
    induction H2; eSearch.
Qed.

#[export] Hint Resolve duality : main.

(*
  Swapping the trusted and exported predicates in an admissibility graph
  results in flipping the direction of the allowed dependencies.
*)

Theorem transposition :
  forall (node : Type) (g1 g2 : admissibilityGraph node),
  (forall n, trusted g1 n <-> exported g2 n) ->
  (forall n, exported g1 n <-> trusted g2 n) ->
  (forall n1 n2, member g1 n1 n2 <-> member g2 n1 n2) ->
  forall n1 n2, allowed g1 n1 n2 <-> allowed g2 n2 n1.
Proof.
  split; apply duality.
  - apply H.
  - apply H0.
  - apply H1.
  - clean.
    apply <- H0.
    search.
  - clean.
    apply <- H.
    search.
  - apply H1.
Qed.

#[export] Hint Resolve transposition : main.

(**************************)
(**************************)
(****                  ****)
(****   Proxy graphs   ****)
(****                  ****)
(**************************)
(**************************)

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
  Nodes are related by child-parent edges. Nodes may optionally allow egress
  and/or ingress through their parents.
*)

Record proxyGraph (node : Type) := {
  edge : node -> node -> Prop;
  egress : node -> Prop;
  ingress : node -> Prop;
}.

Arguments edge {_} _ _.
Arguments egress {_} _.
Arguments ingress {_} _.

(*
  Via the following relation, a proxy graph specifies which dependencies
  between the nodes should be allowed.
*)

Inductive allowed {node} (g : proxyGraph node) (n : node) : node -> Prop :=
| reflexivity : allowed g n n
| egressExtension :
    forall n1 n2,
    egress g n ->
    edge g n n1 ->
    allowed g n1 n2 ->
    allowed g n n2
| ingressExtension :
    forall n1 n2,
    ingress g n2 ->
    edge g n2 n1 ->
    allowed g n n1 ->
    allowed g n n2.

#[export] Hint Constructors allowed : main.

(*
  The following theorem gives an equivalent way to characterize which
  dependencies should be allowed.
*)

Theorem admission :
  forall (node : Type) (g : proxyGraph node) n1 n2,
  allowed g n1 n2 <->
  exists n3,
    clos_refl_trans (fun n3 n4 => edge g n3 n4 /\ egress g n3) n1 n3 /\
    clos_refl_trans (fun n3 n4 => edge g n4 n3 /\ ingress g n4) n3 n2.
Proof.
  split; clean.
  - induction H; eSearch; destruct IHallowed; exists x; split; eSearch.
  - pose proof (
      clos_rt_rt1n node (fun n3 n4 => edge g n3 n4 /\ egress g n3) n1 x H
    ).
    pose proof (
      clos_rt_rtn1 node (fun n3 n4 => edge g n4 n3 /\ ingress g n4) x n2 H0
    ).
    clear H H0.
    induction H1; induction H2; eSearch.
Qed.

#[export] Hint Resolve admission : main.

(*
  Given two proxy graphs with the same set of nodes and edges such that nodes
  that allow ingress through their parents in the first graph allow egress
  through their parents in the second graph and nodes that allow egress through
  their parents in the first graph allow ingress through their parents in the
  second graph, the second graph allows flipped versions of any dependencies
  allowed by the first graph.
*)

Theorem duality :
  forall (node : Type) (g1 g2 : proxyGraph node),
  (forall n, egress g1 n -> ingress g2 n) ->
  (forall n, ingress g1 n -> egress g2 n) ->
  (forall n1 n2, edge g1 n1 n2 -> edge g2 n1 n2) ->
  forall n1 n2, allowed g1 n1 n2 -> allowed g2 n2 n1.
Proof.
  clean.
  destruct (admission node g1 n1 n2).
  clear H4.
  specialize (H3 H2).
  do 2 destruct H3.
  apply admission.
  exists x.
  split.
  - clear H H2.
    apply clos_rt_rt1n in H3.
    induction H3; eSearch.
    induction H4; eSearch.
  - clear H0 H2.
    apply clos_rt_rtn1 in H4.
    induction H4; eSearch.
    induction H3; eSearch.
Qed.

#[export] Hint Resolve duality : main.

(*
  Swapping the ingress and egress predicates in a proxy graph results in
  flipping the direction of the allowed dependencies.
*)

Theorem transposition :
  forall (node : Type) (g1 g2 : proxyGraph node),
  (forall n, egress g1 n <-> ingress g2 n) ->
  (forall n, ingress g1 n <-> egress g2 n) ->
  (forall n1 n2, edge g1 n1 n2 <-> edge g2 n1 n2) ->
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

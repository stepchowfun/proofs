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
  A proxy graph has two types of directed edges: egress extension and ingress
  extension.
*)

Record proxyGraph (node : Type) := {
  egress : node -> node -> Prop;
  ingress : node -> node -> Prop;
}.

Arguments egress {_} _ _.
Arguments ingress {_} _ _.

(*
  Via the following relation, a proxy graph specifies which dependencies
  between the nodes should be allowed.
*)

Inductive admits {node} (g : proxyGraph node) (n : node) : node -> Prop :=
| reflexivity : admits g n n
| egressExtension :
    forall n1 n2, egress g n n1 -> admits g n1 n2 -> admits g n n2
| ingressExtension :
    forall n1 n2, admits g n n1 -> ingress g n1 n2 -> admits g n n2.

#[export] Hint Constructors admits : main.

(*
  The following theorem gives an equivalent way to characterize which
  dependencies should be allowed.
*)

Theorem admission :
  forall (node : Type) (g : proxyGraph node) n1 n2,
  admits g n1 n2 <->
  exists n3,
    clos_refl_trans (egress g) n1 n3 /\ clos_refl_trans (ingress g) n3 n2.
Proof.
  split; clean.
  - induction H; eSearch.
  - pose proof (clos_rt_rt1n node (egress g) n1 x H).
    pose proof (clos_rt_rtn1 node (ingress g) x n2 H0).
    clear H H0.
    induction H1; induction H2; eSearch.
Qed.

#[export] Hint Resolve admission : main.

(*
  Given two proxy graphs with the same set of nodes such that edge in the first
  graph imply corresponding edges of the opposite type and in the opposite
  direction in the second graph, then the second graph allows flipped versions
  of any dependencies allowed by the first graph.
*)

Theorem duality :
  forall (node : Type) (g1 g2 : proxyGraph node),
  (forall n1 n2, egress g1 n1 n2 -> ingress g2 n2 n1) ->
  (forall n1 n2, ingress g1 n1 n2 -> egress g2 n2 n1) ->
  forall n1 n2, admits g1 n1 n2 -> admits g2 n2 n1.
Proof.
  clean.
  destruct (admission node g1 n1 n2).
  clear H3.
  specialize (H2 H1).
  do 2 destruct H2.
  apply admission.
  exists x.
  split.
  - clear H H2.
    apply clos_rt_rt1n in H3.
    induction H3; eSearch.
  - clear H0 H3.
    apply clos_rt_rtn1 in H2.
    induction H2; eSearch.
Qed.

#[export] Hint Resolve duality : main.

(**********************************)
(**********************************)
(****                          ****)
(****   Admissibility graphs   ****)
(****                          ****)
(**********************************)
(**********************************)

Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.
Require Import main.tactics.

#[local] Arguments clos_refl_trans [A] _ _ _.
#[local] Arguments clos_refl_trans_1n [A] _ _ _.
#[local] Arguments clos_refl_trans_n1 [A] _ _ _.
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

Record AdmissibilityGraph (Node : Type) := {
  Trusts : Node -> Node -> Prop;
  Exports : Node -> Node -> Prop;
}.

Arguments Trusts [_] _ _.
Arguments Exports [_] _ _.

(*
  Every node may depend on itself, the nodes it trusts, the nodes that export
  it, any node that a node that trusts it can depend on, and any node that is
  exported by a node that it can depend on.
*)

Inductive Allowed [Node] (g : AdmissibilityGraph Node) (n : Node) : Node
  -> Prop :=
| loop : Allowed g n n
| trust : forall n1, Trusts g n n1 -> Allowed g n n1
| export : forall n1, Exports g n1 n -> Allowed g n n1
| egress : forall n1 n2, Trusts g n1 n -> Allowed g n1 n2 -> Allowed g n n2
| ingress : forall n1 n2, Exports g n1 n2 -> Allowed g n n1 -> Allowed g n n2.

#[export] Hint Constructors Allowed : main.

(*
  Given two admissibility graphs with the same nodes that have matching edges
  between all pairs of *distinct* nodes, then they allow the same dependencies.
  In other words, nothing is gained by having a node trust or export itself.
*)

Theorem reflection :
  forall (Node : Type) (g1 g2 : AdmissibilityGraph Node),
  (forall n1 n2, n1 = n2 \/ (Trusts g1 n1 n2 <-> Trusts g2 n1 n2)) ->
  (forall n1 n2, n1 = n2 \/ (Exports g1 n1 n2 <-> Exports g2 n1 n2)) ->
  forall n1 n2, Allowed g1 n1 n2 <-> Allowed g2 n1 n2.
Proof.
  split; clean.
  - induction H1; search.
    + specialize (H n n1).
      search.
    + specialize (H0 n1 n).
      search.
    + specialize (H n1 n).
      esearch.
    + specialize (H0 n1 n2).
      esearch.
  - induction H1; search.
    + specialize (H n n1).
      search.
    + specialize (H0 n1 n).
      search.
    + specialize (H n1 n).
      esearch.
    + specialize (H0 n1 n2).
      esearch.
Qed.

#[export] Hint Resolve reflection : main.

(*
  The following theorem gives an equivalent way to characterize which
  dependencies should be allowed.
*)

Theorem admission :
  forall (Node : Type) (g : AdmissibilityGraph Node) n1 n2,
  Allowed g n1 n2 <->
  exists n3 n4,
    clos_refl_trans (fun n5 n6 => Trusts g n6 n5) n1 n3 /\
    (n3 = n4 \/ Trusts g n3 n4 \/ Exports g n4 n3) /\
    clos_refl_trans (fun n5 n6 => Exports g n5 n6) n4 n2.
Proof.
  split; clean.
  - induction H.
    + exists n, n.
      search.
    + exists n, n1.
      search.
    + exists n, n1.
      search.
    + destruct IHAllowed.
      destruct H1.
      exists x, x0.
      esearch.
    + destruct IHAllowed.
      destruct H1.
      exists x, x0.
      esearch.
  - induction (clos_rt_rt1n Node (fun n5 n6 => Trusts g n6 n5) n1 x H);
    induction (clos_rt_rtn1 Node (fun n5 n6 => Exports g n5 n6) x0 n2 H1);
    esearch.
Qed.

#[export] Hint Resolve admission : main.

(*
  Given two admissibility graphs with the same set of nodes such that edges in
  the first graph imply corresponding edges of the opposite type in the second
  graph, then the second graph allows flipped versions of any dependencies
  allowed by the first graph.
*)

Theorem duality :
  forall (Node : Type) (g1 g2 : AdmissibilityGraph Node),
  (forall n1 n2, Trusts g1 n1 n2 -> Exports g2 n1 n2) ->
  (forall n1 n2, Exports g1 n1 n2 -> Trusts g2 n1 n2) ->
  forall n1 n2, Allowed g1 n1 n2 -> Allowed g2 n2 n1.
Proof.
  clean.
  destruct (admission Node g1 n1 n2).
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
    induction H3; esearch.
  - clear H0 H2 H3.
    apply clos_rt_rtn1 in H1.
    induction H1; esearch.
Qed.

#[export] Hint Resolve duality : main.

(*
  Swapping the edge types in an admissibility graph results in flipping the
  direction of the allowed dependencies.
*)

Theorem transposition :
  forall (Node : Type) (g1 g2 : AdmissibilityGraph Node),
  (forall n1 n2, Trusts g1 n1 n2 <-> Exports g2 n1 n2) ->
  (forall n1 n2, Exports g1 n1 n2 <-> Trusts g2 n1 n2) ->
  forall n1 n2, Allowed g1 n1 n2 <-> Allowed g2 n2 n1.
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

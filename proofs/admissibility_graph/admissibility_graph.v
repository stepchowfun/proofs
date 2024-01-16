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
  If there is a (possibly empty) chain of trust from one node to another, we
  say the former is *trusting* of the latter. Likewise, if there is a (possibly
  empty) chain of exports from one node to another, we say the former is
  *exporting* the latter.
*)

Definition Trusting [Node] (g : AdmissibilityGraph Node) n1 n2 :=
  clos_refl_trans (Trusts g) n1 n2.

Definition Exporting [Node] (g : AdmissibilityGraph Node) n1 n2 :=
  clos_refl_trans (Exports g) n1 n2.

(*
  Every node can depend on itself, the nodes it trusts, the nodes that export
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
    Trusting g n3 n1 /\
    Exporting g n4 n2 /\
    (n3 = n4 \/ Trusts g n3 n4 \/ Exports g n4 n3).
Proof.
  unfold Trusting, Exporting.
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
  - induction (clos_rt_rtn1 Node (Trusts g) x n1 H);
    induction (clos_rt_rtn1 Node (Exports g) x0 n2 H0);
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
  unfold Trusting, Exporting in *.
  exists x0, x.
  repeat split; search.
  - clear H H1 H3.
    apply clos_rt_rt1n in H2.
    induction H2; esearch.
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

(*
  If a node trusts or exports another node, we say the former node is a
  *parent* of the latter and the latter is a child of the former.
*)

Definition ParentChild [Node] (g : AdmissibilityGraph Node) (n1 n2 : Node) :=
  Trusts g n1 n2 \/ Exports g n1 n2.

(*
  An important special case which enables additional reasoning power at the
  expense of flexibility is to restrict the graph to a directed forest. The
  resulting structure is called a *wooden admissibility graph*.
*)

Definition Wooden [Node] (g : AdmissibilityGraph Node) :=
  forall n1 n2 n3, ParentChild g n1 n3 -> ParentChild g n2 n3 -> n1 = n2.

(*
  If there is a (possibly empty) chain of lineage from one node to another, we
  say the former is an *ancestor* of the latter.
*)

Definition Ancestor [Node] (g : AdmissibilityGraph Node) n1 n2 :=
  clos_refl_trans (ParentChild g) n1 n2.

(*
  In a wooden admissibility graph, the nodes which can depend on a trusted
  child of a node have that parent as an ancestor or gain access via the child
  being exported by the parent.
*)

Theorem encapsulation :
  forall (Node : Type) (g : AdmissibilityGraph Node) n1 n2 n3,
  Wooden g ->
  Trusts g n1 n2 ->
  Allowed g n3 n2 ->
  Ancestor g n1 n3 \/ (Exports g n1 n2 /\ Allowed g n3 n1).
Proof.
  clean.
  induction H1; search.
  - left.
    assert (n1 = n); search.
    unfold Wooden in H.
    apply H with (n3 := n0); search.
  - left.
    apply rt_trans with (y := n0); search.
  - feed IHAllowed.
    destruct IHAllowed; esearch.
    left.
    apply rt_trans with (y := n0); search.
  - right.
    specialize (H n0 n1 n2).
    do 2 feed H.
Qed.

#[export] Hint Resolve encapsulation : main.

(*
  In a wooden admissibility graph, the nodes which can be depended on by an
  exported child of a node have that parent as an ancestor or grant access via
  the child being trusted by the parent.
*)

Theorem sandboxing :
  forall (Node : Type) (g : AdmissibilityGraph Node) n1 n2 n3,
  Wooden g ->
  Exports g n1 n2 ->
  Allowed g n2 n3 ->
  Ancestor g n1 n3 \/ (Trusts g n1 n2 /\ Allowed g n1 n3).
Proof.
  clean.
  induction H1; search.
  - left.
    apply rt_trans with (y := n); search.
  - assert (n0 = n1); search.
    unfold Wooden in H.
    apply H with (n3 := n); search.
  - right.
    specialize (H n0 n1 n).
    do 2 feed H.
  - feed IHAllowed.
    destruct IHAllowed; esearch.
    left.
    apply rt_trans with (y := n0); search.
Qed.

#[export] Hint Resolve sandboxing : main.

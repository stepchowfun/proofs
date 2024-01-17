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
  The *transpose* of an admissibility graph is the result of swapping the edge
  types.
*)

Definition transpose [Node] (g : AdmissibilityGraph Node) :=
  {|
    Trusts := g.(Exports);
    Exports := g.(Trusts);
  |}.

Theorem transpose_involution :
  forall (Node : Type) (g : AdmissibilityGraph Node),
  g = transpose (transpose g).
Proof.
  search.
Qed.

#[export] Hint Resolve transpose_involution : main.

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

Theorem transpose_trusting :
  forall (Node : Type) (g : AdmissibilityGraph Node),
  Trusting g = Exporting (transpose g).
Proof.
  clean.
  assert (forall n1 n2, Trusting g n1 n2 = Exporting (transpose g) n1 n2);
    search.
Qed.

#[export] Hint Resolve transpose_trusting : main.

Theorem transpose_exporting :
  forall (Node : Type) (g : AdmissibilityGraph Node),
  Exporting g = Trusting (transpose g).
Proof.
  clean.
  assert (forall n1 n2, Exporting g n1 n2 = Trusting (transpose g) n1 n2);
    search.
Qed.

#[export] Hint Resolve transpose_trusting : main.

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
  The dependencies allowed by the transpose of a graph are the flipped versions
  of the dependencies allowed by the original graph.
*)

Theorem transposition :
  forall (Node : Type) (g : AdmissibilityGraph Node) n1 n2,
  Allowed g n1 n2 <-> Allowed (transpose g) n2 n1.
Proof.
  split; clean; induction H; esearch.
Qed.

#[export] Hint Resolve transposition : main.

(*
  If a node trusts or exports another node, we say the former node is a
  *parent* of the latter and the latter is a child of the former.
*)

Definition ParentChild [Node] (g : AdmissibilityGraph Node) (n1 n2 : Node) :=
  Trusts g n1 n2 \/ Exports g n1 n2.

Theorem transpose_parent_child :
  forall (Node : Type) (g : AdmissibilityGraph Node) n1 n2,
  ParentChild g n1 n2 <-> ParentChild (transpose g) n1 n2.
Proof.
  unfold ParentChild.
  search.
Qed.

#[export] Hint Resolve transpose_parent_child : main.

(*
  If there is a (possibly empty) chain of lineage from one node to another, we
  say the former is an *ancestor* of the latter.
*)

Definition Ancestor [Node] (g : AdmissibilityGraph Node) n1 n2 :=
  clos_refl_trans (ParentChild g) n1 n2.

Theorem transpose_ancestor :
  forall (Node : Type) (g : AdmissibilityGraph Node) n1 n2,
  Ancestor g n1 n2 <-> Ancestor (transpose g) n1 n2.
Proof.
  split; clean.
  - induction H; search.
    + apply rt_step.
      apply -> transpose_parent_child.
      search.
    + apply rt_trans with (y := y); search.
  - induction H; search.
    + apply rt_step.
      apply transpose_parent_child in H.
      search.
    + apply rt_trans with (y := y); search.
Qed.

#[export] Hint Resolve transpose_parent_child : main.

(* The ancestor relation is a superset of the trusting relation. *)

Theorem trustingAncestor [Node] (g : AdmissibilityGraph Node) n1 n2 :
  Trusting g n1 n2 -> Ancestor g n1 n2.
Proof.
  clean.
  induction H; search.
  apply rt_trans with (y := y); search.
Qed.

#[export] Hint Resolve trustingAncestor : main.

(* The ancestor relation is a superset of the exporting relation. *)

Theorem exportingAncestor [Node] (g : AdmissibilityGraph Node) n1 n2 :
  Exporting g n1 n2 -> Ancestor g n1 n2.
Proof.
  clean.
  induction H; search.
  apply rt_trans with (y := y); search.
Qed.

#[export] Hint Resolve exportingAncestor : main.

(*
  An important special case which enables additional reasoning power at the
  expense of flexibility is to restrict the graph to a directed forest. The
  resulting structure is called a *wooden admissibility graph*.
*)

Definition Wooden [Node] (g : AdmissibilityGraph Node) :=
  forall n1 n2 n3, ParentChild g n1 n3 -> ParentChild g n2 n3 -> n1 = n2.

Theorem transpose_wooden :
  forall (Node : Type) (g : AdmissibilityGraph Node),
  Wooden g <-> Wooden (transpose g).
Proof.
  unfold Wooden.
  split; clean.
  - apply <- transpose_parent_child in H0.
    apply <- transpose_parent_child in H1.
    esearch.
  - apply transpose_parent_child in H0.
    apply transpose_parent_child in H1.
    esearch.
Qed.

#[export] Hint Resolve transpose_wooden : main.

(*
  In a wooden admissibility graph, the following three situations characterize
  which nodes can depend on the children of a parent:

  1. The nodes that the parent is trusting of can depend on the children of the
     parent.
  2. Nodes that can depend on the parent can depend on its exported children.
  3. The children can be depended on by their own exported children and the
     nodes that those exported children are trusting of.
*)

Theorem childIngress :
  forall (Node : Type) (g : AdmissibilityGraph Node) n1 n2 n3,
  Wooden g ->
  ParentChild g n1 n2 ->
  (
    Allowed g n3 n2 <->
    Trusting g n1 n3 \/
    (Exports g n1 n2 /\ Allowed g n3 n1) \/
    (exists n4, Exports g n2 n4 /\ Trusting g n4 n3)
  ).
Proof.
  split; clean.
  - destruct H0.
    + induction H1; search.
      * left.
        assert (n1 = n); search.
        unfold Wooden in H.
        apply H with (n3 := n0); search.
      * do 2 right.
        exists n.
        search.
      * feed IHAllowed.
        destruct IHAllowed; search.
        -- left.
           apply rt_trans with (y := n0); search.
        -- destruct H3; esearch.
           do 2 destruct H3.
           do 2 right.
           exists x.
           split; search.
           apply rt_trans with (y := n0); search.
      * right.
        specialize (H n0 n1 n2).
        do 2 feed H.
    + induction H1; search.
      * left.
        assert (n1 = n); search.
        unfold Wooden in H.
        apply H with (n3 := n0); search.
      * do 2 right.
        exists n.
        search.
      * feed IHAllowed.
        destruct IHAllowed; search.
        -- left.
           apply rt_trans with (y := n0); search.
        -- destruct H3; esearch.
           do 2 destruct H3.
           do 2 right.
           exists x.
           split; search.
           apply rt_trans with (y := n0); search.
      * right.
        specialize (H n0 n1 n2).
        do 2 feed H.
  - destruct H0.
    + destruct H1; search.
      * apply admission.
        exists n1, n2.
        search.
      * destruct H1; esearch.
        do 2 destruct H1.
        apply admission.
        exists x, n2.
        search.
    + destruct H1; search.
      * apply admission.
        exists n1, n1.
        search.
      * destruct H1; esearch.
        do 2 destruct H1.
        apply admission.
        exists x, n2.
        search.
Qed.

#[export] Hint Resolve childIngress : main.

(*
  An important consequence of the previous theorem: in a wooden admissibility
  graph, the nodes which can depend on a child of a parent have that parent as
  an ancestor or the child is exported and ingress is via the parent.
*)

Theorem encapsulation :
  forall (Node : Type) (g : AdmissibilityGraph Node) n1 n2 n3,
  Wooden g ->
  ParentChild g n1 n2 ->
  Allowed g n3 n2 ->
  Ancestor g n1 n3 \/ (Exports g n1 n2 /\ Allowed g n3 n1).
Proof.
  clean.
  pose proof (childIngress Node g n1 n2 n3 H H0).
  destruct H2.
  clear H3.
  feed H2.
  destruct H2; search.
  destruct H2; search.
  do 2 destruct H2.
  left.
  apply rt_trans with (y := n2); search.
  apply rt_trans with (y := x); search.
  apply trustingAncestor.
  search.
Qed.

#[export] Hint Resolve encapsulation : main.

(*
  In a wooden admissibility graph, the following three situations characterize
  which nodes the children of a parent can depend on:

  1. The children of the parent can depend on the nodes that the parent is
     exporting.
  2. The trusted children of the parent can depend on nodes that the parent can
     depend on.
  3. The children can depend on their own trusted children and the nodes that
     those trusted children are exporting.
*)

Theorem childEgress :
  forall (Node : Type) (g : AdmissibilityGraph Node) n1 n2 n3,
  Wooden g ->
  ParentChild g n1 n2 ->
  (
    Allowed g n2 n3 <->
    Exporting g n1 n3 \/
    (Trusts g n1 n2 /\ Allowed g n1 n3) \/
    (exists n4, Trusts g n2 n4 /\ Exporting g n4 n3)
  ).
Proof.
  split; clean.
  - pose proof (childIngress Node (transpose g) n1 n2 n3).
    feed H2; [ apply -> transpose_wooden; search | idtac ].
    feed H2; [ apply -> transpose_parent_child; search | idtac ].
    destruct H2.
    clear H3.
    feed H2.
    + apply -> transposition.
      search.
    + clean.
      rewrite <- transpose_exporting in H2.
      repeat (destruct H2; search).
      apply transposition in H3.
      search.
  - pose proof (childIngress Node (transpose g) n1 n2 n3).
    feed H2; [ apply -> transpose_wooden; search | idtac ].
    feed H2; [ apply -> transpose_parent_child; search | idtac ].
    destruct H2.
    clear H2.
    apply transposition in H3; search.
Qed.

#[export] Hint Resolve childEgress : main.

(*
  An important consequence of the previous theorem: in a wooden admissibility
  graph, the nodes which can be depended on by an exported child of a parent
  have that parent as an ancestor or the child is trusted and egress is via the
  parent.
*)

Theorem sandboxing :
  forall (Node : Type) (g : AdmissibilityGraph Node) n1 n2 n3,
  Wooden g ->
  ParentChild g n1 n2 ->
  Allowed g n2 n3 ->
  Ancestor g n1 n3 \/ (Trusts g n1 n2 /\ Allowed g n1 n3).
Proof.
  clean.
  pose proof (encapsulation Node (transpose g) n1 n2 n3).
  feed H2; [ apply -> transpose_wooden; search | idtac ].
  feed H2; [ apply -> transpose_parent_child; search | idtac ].
  feed H2; [ apply -> transposition; search | idtac ].
  destruct H2.
  - apply transpose_ancestor in H2.
    search.
  - clean.
    apply transposition in H3.
    search.
Qed.

#[export] Hint Resolve sandboxing : main.

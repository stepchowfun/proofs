(******************************)
(******************************)
(****                      ****)
(****   Ownership graphs   ****)
(****                      ****)
(******************************)
(******************************)

Require Import Main.Tactics.

Section OwnershipGraph.

  (* The vertices of the graph, e.g., users, documents, etc. *)
  Variable node : Type.

  (* The edges of the graph, e.g., links between documents *)
  Variable edge : node -> node -> Prop.

  (*
    This relation indicates when one node directly "owns" another. It can be
    understood as another type of edge. Note that:
    - A node may have multiple owners.
    - There can be cycles of ownership.
  *)
  Variable owns : node -> node -> Prop.

  (*
    We'd like ownership to be a preorder, so here we define the transitive
    reflexive closure of the `owns` relation.
  *)
  Inductive supervises (n1 : node) : node -> Prop :=
  | supervisesRefl :
    supervises n1 n1
  | supervisesCons :
    forall n2 n3,
    supervises n1 n2 ->
    owns n2 n3 ->
    supervises n1 n3.

  Hint Constructors supervises : main.

  (*
    The next two theorems establish that `supervises` is indeed a preorder.
  *)

  Theorem supervisesReflexive :
    forall n1, supervises n1 n1.
  Proof.
    magic.
  Qed.

  Theorem supervisesTransitive :
    forall n1 n2 n3,
    supervises n1 n2 ->
    supervises n2 n3 ->
    supervises n1 n3.
  Proof.
    clean.
    induction H0; magic.
    apply supervisesCons with (n2 := n0); auto.
  Qed.

  (*
    For any given node, we'd like the subgraph induced by the set of nodes
    supervised by that node to be reachable by that node. To that end, we
    introduce the following `manages` relation as a refinement of the
    `supervises` relation.
  *)
  Inductive manages (n1 : node) : node -> Prop :=
  | managesRefl :
    manages n1 n1
  | managesCons :
    forall n2 n3,
    manages n1 n2 ->
    supervises n2 n3 ->
    edge n2 n3 ->
    manages n1 n3.

  Hint Constructors manages : main.

  (* The next two theorems establish that `manages` is a preorder. *)

  Theorem managesReflexive : forall n1, manages n1 n1.
  Proof.
    magic.
  Qed.

  Theorem managesTransitive :
    forall n1 n2 n3,
    manages n1 n2 ->
    manages n2 n3 ->
    manages n1 n3.
  Proof.
    clean.
    induction H0; magic.
    apply managesCons with (n2 := n0); magic.
  Qed.

  (*
    The following two propositions establish that management and supervision
    should be equivalent. The first is a theorem, and the second is an
    invariant that must be carefully maintained. Informally, the invariant
    states that there are no extraneous `owns` edges.
  *)

  Theorem managesSound :
    forall n1 n2, manages n1 n2 -> supervises n1 n2.
  Proof.
    clean.
    induction H; magic.
    apply supervisesTransitive with (n2 := n2); magic.
  Qed.

  Hypothesis managesComplete :
    forall n1 n2, supervises n1 n2 -> manages n1 n2.

  (* For uniformity, let there be a universal manager for the whole graph. *)

  Variable root : node.

  Hypothesis rootManagesAll : forall n, manages root n.

End OwnershipGraph.

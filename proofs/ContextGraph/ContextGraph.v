(****************************)
(****************************)
(****                    ****)
(****   Context graphs   ****)
(****                    ****)
(****************************)
(****************************)

Require Import Main.Tactics.

Section ContextGraph.

  (* An *context graph* has a set of nodes, just like any graph. *)

  Variable node : Set.

  (*
    Context graphs are directed, i.e., every edge is associated with a source
    node and a target node. Each edge is also labeled with another node which
    is called its *context*. Every node induces a subgraph defined by the
    subset of edges which have that node as their context together with any
    nodes which are their endpoints. Here, edges are indicated by a predicate
    parameterized by the context, source, and target, respectively.
    Specializing the predicate on a particular context yields the binary edge
    relation for the subgraph induced by that context.
  *)

  Variable edge : node -> node -> node -> Prop.

  (*
    A node is *rooted in* a context if it's reachable from that context in the
    subgraph induced by that context. This predicate is used to define a well-
    formedness condition below.
  *)

  Inductive rooted (context : node) : node -> Prop :=
  | loop :
    rooted context context
  | extension :
    forall source target,
    rooted context source ->
    edge context source target ->
    rooted context target.

  #[local] Hint Constructors rooted : main.

  (*
    For a context graph to be *well-formed*, it must satisfy the following
    condition: the source of every edge is rooted in that edge's context.
  *)

  Hypothesis sourcesRooted :
    forall context source target,
    edge context source target ->
    rooted context source.

  (*
    The condition above immediately implies the following as a corollary: the
    target of every edge is rooted in that edge's context.
  *)

  Theorem targetsRooted :
    forall context source target,
    edge context source target ->
    rooted context target.
  Proof.
    clean.
    apply extension with (source := source); magic.
    apply sourcesRooted with (target := target).
    magic.
  Qed.

  (*
    A node is *accessible* from a context if it is that context or if it's
    rooted in a nested context which is accessible from that context.
  *)

  Inductive accessible (context : node) : node -> Prop :=
  | identity :
    accessible context context
  | nested :
    forall nestedContext node,
    accessible context nestedContext ->
    rooted nestedContext node ->
    accessible context node.

  #[local] Hint Constructors accessible : main.

  (* These two theorems establish that accessibility is a preorder. *)

  Theorem accessibleReflexive : forall node, accessible node node.
  Proof.
    magic.
  Qed.

  Theorem accessibleTransitive :
    forall node1 node2 node3,
    accessible node1 node2 ->
    accessible node2 node3 ->
    accessible node1 node3.
  Proof.
    clean.
    induction H0; magic.
    apply nested with (nestedContext := nestedContext); magic.
  Qed.

  (*
    Since the nodes of the subgraph induced by a context must be rooted in that
    context, one might also expect a similar situation for the graph as a
    whole. Here we formalize that criterion by postulating the existence of a
    global context from which every node is accessible.
  *)

  Variable origin : node.

  Hypothesis originality : forall node, accessible origin node.

End ContextGraph.

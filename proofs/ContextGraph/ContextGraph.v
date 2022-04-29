(****************************)
(****************************)
(****                    ****)
(****   Context graphs   ****)
(****                    ****)
(****************************)
(****************************)

Require Import Main.Tactics.

Section ContextGraph.

  (* A *context graph* has a set of nodes, just like any graph. *)

  Variable node : Set.

  (*
    Context graphs are directed, i.e., each edge is associated with a source
    node and a target node. Each edge is also labeled with another node called
    its *context*. Here, edges are indicated by a predicate on the context,
    source, and target, respectively. Specializing the predicate on a
    particular context yields a binary edge relation which induces a subgraph
    for that context.
  *)

  Variable edge : node -> node -> node -> Prop.

  (*
    *Interior reachability* is the transitive reflexive closure of the edge
    relation specialized on a particular context. Reflexivity is immediate from
    the definition, and transitivity is proven below.
  *)

  Inductive interiorReachable (context : node) (start : node) : node -> Prop :=
  | interiorReflexivity :
    interiorReachable context start start
  | interiorExtension :
    forall source target,
    interiorReachable context start source ->
    edge context source target ->
    interiorReachable context start target.

  #[local] Hint Constructors interiorReachable : main.

  (* Interior reachability contains the edge relation. *)

  Theorem interiorReachableComplete :
    forall context source target,
    edge context source target ->
    interiorReachable context source target.
  Proof.
    clean.
    apply interiorExtension with (source := source); magic.
  Qed.

  (*
    Interior reachability is reflexive by definition. Here, we show that it's
    also transitive and thus a preorder.
  *)

  Theorem interiorTransitivity :
    forall context node1 node2 node3,
    interiorReachable context node1 node2 ->
    interiorReachable context node2 node3 ->
    interiorReachable context node1 node3.
  Proof.
    clean.
    induction H0; magic.
    apply interiorExtension with (source := source); magic.
  Qed.

  (*
    A node is *rooted in* a context if it's interior reachable in and from that
    context.
  *)

  Definition rooted context := interiorReachable context context.

  (*
    For a context graph to be *well-formed*, it must satisfy the following
    condition: the source of every edge is rooted in that edge's context.
  *)

  Hypothesis sourcesRooted :
    forall context source target,
    edge context source target ->
    rooted context source.

  (*
    The condition above immediately implies the following corollary: the target
    of every edge is rooted in that edge's context.
  *)

  Theorem targetsRooted :
    forall context source target,
    edge context source target ->
    rooted context target.
  Proof.
    clean.
    apply interiorExtension with (source := source); magic.
    apply sourcesRooted with (target := target).
    magic.
  Qed.

  (*
    *Exterior reachability* is the transitive reflexive closure of the rooted
    relation. Reflexivity is immediate from the definition, and transitivity is
    proven below.
  *)

  Inductive exteriorReachable (start : node) : node -> Prop :=
  | exteriorReflexivity :
    exteriorReachable start start
  | exteriorExtension :
    forall context node,
    exteriorReachable start context ->
    rooted context node ->
    exteriorReachable start node.

  #[local] Hint Constructors exteriorReachable : main.

  (* Exterior reachability contains the rooted relation. *)

  Theorem exteriorReachableComplete :
    forall context node, rooted context node -> exteriorReachable context node.
  Proof.
    clean.
    apply exteriorExtension with (context := context); magic.
  Qed.

  (*
    Exterior reachability is reflexive by definition. Here, we show that it's
    also transitive and thus a preorder.
  *)

  Theorem exteriorTransitivity :
    forall node1 node2 node3,
    exteriorReachable node1 node2 ->
    exteriorReachable node2 node3 ->
    exteriorReachable node1 node3.
  Proof.
    clean.
    induction H0; magic.
    apply exteriorExtension with (context := context); magic.
  Qed.

  (*
    Since the nodes of the subgraph induced by the edges for a particular
    context must be rooted in that context, one might also expect an analogous
    situation for the graph as a whole. Here we formalize that criterion by
    postulating the existence of an *origin* context from which every node is
    exterior reachable.
  *)

  Variable origin : node.

  Hypothesis originality : forall node, exteriorReachable origin node.

End ContextGraph.

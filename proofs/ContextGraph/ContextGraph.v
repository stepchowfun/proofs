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
    Unsurprisingly, a context graph also has edges. In our formulation, edges
    are directed, but this is inessential.

    Each edge in a context graph is labeled with a node called its *context*.
    We indicate edges by ternary relation between the context, source, and
    target, respectively. Specializing the ternary relation on a particular
    context yields a binary edge relation which induces a subgraph associated
    with that context.
  *)

  Variable edge : node -> node -> node -> Prop.

  (*
    *Horizontal reachability* is the transitive reflexive closure of the edge
    relation specialized on a particular context. Reflexivity is immediate from
    the definition, and transitivity is proven below.
  *)

  Inductive horizontallyReachable
    (context : node) (start : node) : node -> Prop :=
  | horizontalReflexivity :
    horizontallyReachable context start start
  | horizontalExtension :
    forall source target,
    horizontallyReachable context start source ->
    edge context source target ->
    horizontallyReachable context start target.

  #[local] Hint Constructors horizontallyReachable : main.

  (* Horizontal reachability contains the edge relation. *)

  Theorem horizontalCompleteness :
    forall context source target,
    edge context source target ->
    horizontallyReachable context source target.
  Proof.
    clean.
    apply horizontalExtension with (source := source); magic.
  Qed.

  (*
    Horizontal reachability is reflexive by definition. Here, we show that it's
    also transitive and thus a preorder.
  *)

  Theorem horizontalTransitivity :
    forall context node1 node2 node3,
    horizontallyReachable context node1 node2 ->
    horizontallyReachable context node2 node3 ->
    horizontallyReachable context node1 node3.
  Proof.
    clean.
    induction H0; magic.
    apply horizontalExtension with (source := source); magic.
  Qed.

  (*
    A node is *rooted in* a context if it's horizontally reachable in and from
    that context.
  *)

  Definition rooted context := horizontallyReachable context context.

  (*
    The following requirement establishes the connection between the contexts
    of the edges and the structure of the graph: the source of every edge is
    rooted in that edge's context.
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
    apply horizontalExtension with (source := source); magic.
    apply sourcesRooted with (target := target).
    magic.
  Qed.

  (*
    *Vertical reachability* is the transitive reflexive closure of the rooted
    relation. Reflexivity is immediate from the definition, and transitivity is
    proven below.
  *)

  Inductive verticallyReachable (start : node) : node -> Prop :=
  | verticalReflexivity :
    verticallyReachable start start
  | verticalExtension :
    forall context node,
    verticallyReachable start context ->
    rooted context node ->
    verticallyReachable start node.

  #[local] Hint Constructors verticallyReachable : main.

  (* Vertical reachability contains the rootedness relation. *)

  Theorem verticalCompleteness :
    forall context node,
    rooted context node ->
    verticallyReachable context node.
  Proof.
    clean.
    apply verticalExtension with (context := context); magic.
  Qed.

  (*
    Vertical reachability is reflexive by definition. Here, we show that it's
    also transitive and thus a preorder.
  *)

  Theorem verticalTransitivity :
    forall node1 node2 node3,
    verticallyReachable node1 node2 ->
    verticallyReachable node2 node3 ->
    verticallyReachable node1 node3.
  Proof.
    clean.
    induction H0; magic.
    apply verticalExtension with (context := context); magic.
  Qed.

  (*
    Rootedness is intended to signify nesting. To support that intention, we
    require vertical reachability to be antisymmetric and thus a partial order.
  *)

  Hypothesis verticalAntisymmetry :
    forall node1 node2,
    verticallyReachable node1 node2 ->
    verticallyReachable node2 node1 ->
    node1 = node2.

  (*
    Since the nodes of the subgraph associated with a particular context must
    be rooted in that context, one might also expect an analogous situation for
    the graph as a whole. Here we formalize that criterion by postulating the
    existence of an *origin* context from which every node is vertically
    reachable.
  *)

  Variable origin : node.

  Hypothesis originality : forall node, verticallyReachable origin node.

End ContextGraph.

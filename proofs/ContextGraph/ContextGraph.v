(****************************)
(****************************)
(****                    ****)
(****   Context graphs   ****)
(****                    ****)
(****************************)
(****************************)

Require Import Coq.Relations.Relation_Operators.

Module Type ContextGraph.
  #[local] Arguments clos_refl_trans {A} _ _ _.

  (* A *context graph* has a set of nodes, just like any graph. *)

  Parameter node : Type.

  (*
    In our formulation, edges are directed, but this is inessential.

    Each edge in a context graph is labeled with a node called its *context*.
    We indicate edges by ternary relation between the context, source, and
    target. Specializing the ternary relation on a particular context yields a
    binary edge relation which induces a subgraph associated with that context.
  *)

  Parameter edge : node -> node -> node -> Prop.

  (*
    *Horizontal reachability* in a context is the transitive reflexive closure
    of the edge relation specialized on that context.
  *)

  Definition horizontallyReachable context := clos_refl_trans (edge context).

  (*
    A node is *rooted* in a context if it's horizontally reachable in and from
    that context.
  *)

  Definition rooted context := horizontallyReachable context context.

  (*
    *Vertical reachability* is the transitive reflexive closure of rootedness.
  *)

  Definition verticallyReachable := clos_refl_trans rooted.

  (*
    Rootedness is intended to signify nesting. To codify that intention, we
    require vertical reachability to be antisymmetric and thus a partial order.
  *)

  Axiom verticalAntisymmetry :
    forall node1 node2,
    verticallyReachable node1 node2 ->
    verticallyReachable node2 node1 ->
    node1 = node2.

  (*
    Let there be an *origin* context from which every node is vertically
    reachable.
  *)

  Parameter origin : node.

  Axiom originality : forall node, verticallyReachable origin node.
End ContextGraph.

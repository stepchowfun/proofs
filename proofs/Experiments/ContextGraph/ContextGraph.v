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
    Edges are directed in our formulation, but this is inessential.

    Each edge in a context graph is labeled with a node called its *context*.
    We indicate edges by ternary relation between the context, source, and
    target. Specializing the ternary relation on a particular context yields a
    binary edge relation which induces a subgraph associated with that context.
  *)

  Parameter edge : node -> node -> node -> Prop.

  (*
    *Horizontal reachability* in a context is the reflexive transitive closure
    of the edge relation specialized on that context.
  *)

  Definition horizontallyReachable c := clos_refl_trans (edge c).

  #[export] Hint Unfold horizontallyReachable : main.

  (*
    A context *proxies* a node if the node is horizontally reachable in and
    from that context.
  *)

  Definition proxies c := horizontallyReachable c c.

  #[export] Hint Unfold proxies : main.

  (*
    *Vertical reachability* is the reflexive transitive closure of proxying.
  *)

  Definition verticallyReachable := clos_refl_trans proxies.

  #[export] Hint Unfold verticallyReachable : main.

  (*
    Proxying is intended to signify nesting. To codify that intention, we
    require vertical reachability to be antisymmetric and thus a partial order.
  *)

  Axiom verticalAntisymmetry :
    forall n1 n2,
    verticallyReachable n1 n2 ->
    verticallyReachable n2 n1 ->
    n1 = n2.

  #[export] Hint Resolve verticalAntisymmetry : main.

  (*
    Let there be a *root* context from which every node is vertically
    reachable.
  *)

  Parameter root : node.

  Axiom rootReach : forall n, verticallyReachable root n.

  #[export] Hint Resolve rootReach : main.
End ContextGraph.

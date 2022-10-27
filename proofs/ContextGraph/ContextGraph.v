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
    A node *contains* another node when that other node is horizontally
    reachable in and from it.
  *)

  Definition contains c := horizontallyReachable c c.

  #[export] Hint Unfold contains : main.

  (* The subgraph associated with a context is rooted at that context. *)

  Axiom connectedness : forall c n1 n2, edge c n1 n2 -> contains c n1.

  #[export] Hint Resolve connectedness : main.

  (*
    *Vertical reachability* is the reflexive transitive closure of containment.
  *)

  Definition verticallyReachable := clos_refl_trans contains.

  #[export] Hint Unfold verticallyReachable : main.

  (*
    If there is any sharing between two nodes in a context, that sharing is
    reflected in the context.
  *)

  Axiom abstraction :
    forall c n1 n2 n3,
    contains c n1 ->
    contains c n2 ->
    verticallyReachable n1 n3 ->
    verticallyReachable n2 n3 ->
    edge c n1 n2.

  #[export] Hint Resolve abstraction : main.

  (*
    Containment is intended to signify nesting. To codify that intention, we
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

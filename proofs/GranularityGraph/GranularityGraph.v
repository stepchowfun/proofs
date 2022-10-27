(********************************)
(********************************)
(****                        ****)
(****   Granularity graphs   ****)
(****                        ****)
(********************************)
(********************************)

Require Import Coq.Relations.Relation_Operators.

Module Type GranularityGraph.
  #[local] Arguments clos_refl_trans {A} _ _ _.

  (* A *granularity graph* has a set of nodes, just like any graph. *)

  Parameter node : Type.

  (*
    Edges are directed in our formulation, but this is inessential.

    Each edge in a granularity graph is labeled with a node called its *grain*.
    We indicate edges by ternary relation between the grain, source, and
    target. Specializing the ternary relation on a particular grain yields a
    binary edge relation which induces a subgraph associated with that grain.
  *)

  Parameter edge : node -> node -> node -> Prop.

  (*
    *Horizontal reachability* in a grain is the reflexive transitive closure
    of the edge relation specialized on that grain.
  *)

  Definition horizontallyReachable g := clos_refl_trans (edge g).

  #[export] Hint Unfold horizontallyReachable : main.

  (*
    A grain *contains* a node when that node is horizontally reachable in and
    from the grain.
  *)

  Definition contains g := horizontallyReachable g g.

  #[export] Hint Unfold contains : main.

  (* The subgraph associated with a grain is rooted at that grain. *)

  Axiom containment : forall g n1 n2, edge g n1 n2 -> contains g n1.

  #[export] Hint Resolve containment : main.

  (*
    *Vertical reachability* is the reflexive transitive closure of containment.
  *)

  Definition verticallyReachable := clos_refl_trans contains.

  #[export] Hint Unfold verticallyReachable : main.

  (*
    If there is any sharing between two nodes in a grain, that sharing is
    reflected in the grain.
  *)

  Axiom reflection :
    forall g n1 n2 n3,
    contains g n1 ->
    contains g n2 ->
    verticallyReachable n1 n3 ->
    verticallyReachable n2 n3 ->
    edge g n1 n2.

  #[export] Hint Resolve reflection : main.

  (*
    Containment is intended to signify nesting in some sense. To codify that
    intention, we require vertical reachability to be antisymmetric and thus a
    partial order.
  *)

  Axiom verticalAntisymmetry :
    forall n1 n2,
    verticallyReachable n1 n2 ->
    verticallyReachable n2 n1 ->
    n1 = n2.

  #[export] Hint Resolve verticalAntisymmetry : main.

  (*
    Let there be a *root* grain from which every node is vertically reachable.
  *)

  Parameter root : node.

  Axiom rootReach : forall n, verticallyReachable root n.

  #[export] Hint Resolve rootReach : main.
End GranularityGraph.

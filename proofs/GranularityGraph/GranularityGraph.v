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
    Each edge in a granularity graph is labeled with a node called its *grain*.
    We indicate edges by a ternary relation between the grain, source, and
    target. Specializing the ternary relation on a particular grain yields a
    binary edge relation which induces a subgraph associated with that grain.
  *)

  Parameter edge : node -> node -> node -> Prop.

  (*
    *Reachability in a grain* is the reflexive transitive closure of the edge
    relation specialized on that grain.
  *)

  Definition reachable g := clos_refl_trans (edge g).

  #[export] Hint Unfold reachable : main.

  (*
    A node is *visible at a grain* when it's reachable in and from that grain.
  *)

  Definition visible g := reachable g g.

  #[export] Hint Unfold visible : main.

  (*
    The objects in the subgraph associated with a grain are visible at that
    grain.
  *)

  Axiom visibility : forall g n1 n2, edge g n1 n2 -> visible g n1.

  #[export] Hint Resolve visibility : main.

  (* *Containment* is the reflexive transitive closure of visibility. *)

  Definition contains := clos_refl_trans visible.

  #[export] Hint Unfold contains : main.

  (*
    Any sharing between two nodes visible at the same grain is reflected in
    that grain.
  *)

  Axiom sharing :
    forall g n1 n2 n3,
    visible g n1 ->
    visible g n2 ->
    contains n1 n3 ->
    contains n2 n3 ->
    exists n4,
    edge g n1 n4 /\
    edge g n4 n1 /\
    edge g n2 n4 /\
    edge g n4 n2 /\
    contains n4 n3.

  #[export] Hint Resolve sharing : main.

  (* Containment is antisymmetric and thus a partial order. *)

  Axiom containment :
    forall n1 n2,
    contains n1 n2 ->
    contains n2 n1 ->
    n1 = n2.

  #[export] Hint Resolve containment : main.

  (* There is a *root* grain which contains every node in the graph. *)

  Parameter root : node.

  Axiom rootedness : forall n, contains root n.

  #[export] Hint Resolve rootedness : main.
End GranularityGraph.

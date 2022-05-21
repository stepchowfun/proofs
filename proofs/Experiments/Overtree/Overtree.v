(***********************)
(***********************)
(****               ****)
(****   Overtrees   ****)
(****               ****)
(***********************)
(***********************)

Require Import Coq.Relations.Relation_Operators.

Module Type Overtree.
  #[local] Arguments clos_refl_trans {A} _ _ _.

  (* An *overtree* has a set of nodes, just like any graph. *)

  Parameter node : Type.

  (* Edges are directed in our formulation, but this is inessential. *)

  Parameter edge : node -> node -> Prop.

  (* Each node is associated with a node called its *proxy*. *)

  Parameter proxy : node -> node.

  (* An edge is called *covalent* if its source and target share a proxy. *)

  Definition covalent n1 n2 := edge n1 n2 /\ proxy n1 = proxy n2.

  (*
    *Horizontal reachability* is the transitive reflexive closure of covalency.
  *)

  Definition horizontallyReachable := clos_refl_trans covalent.

  (*
    A node *proxies* another node if it's the proxy for that node and that node
    is horizontally reachable from one of the proxy's neighbors.
  *)

  Definition proxies n1 n2 :=
    proxy n2 = n1 /\
    exists n3,
    edge n1 n3 /\
    horizontallyReachable n3 n2.

  (*
    *Vertical reachability* is the transitive reflexive closure of proxying.
  *)

  Definition verticallyReachable := clos_refl_trans proxies.

  (*
    Let there be a *root* node which has a loop, which is its own proxy, and
    from which every node is vertically reachable.
  *)

  Parameter root : node.

  Axiom rootLoop : edge root root.

  Axiom rootProxy : proxy root = root.

  Axiom rootReach : forall n, verticallyReachable root n.
End Overtree.

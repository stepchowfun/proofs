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

  (* Each node is associated with a node called its *owner*. *)

  Parameter owner : node -> node.

  (* An edge is called *covalent* if its source and target share an owner. *)

  Definition covalent n1 n2 := edge n1 n2 /\ owner n1 = owner n2.

  #[export] Hint Unfold covalent : main.

  (* *Reachability* is the reflexive transitive closure of covalency. *)

  Definition reachable := clos_refl_trans covalent.

  #[export] Hint Unfold reachable : main.

  (*
    A node *owns* another node if it's the owner for that node and that node
    is reachable from one of the owners's neighbors.
  *)

  Definition owns n1 n2 :=
    owner n2 = n1 /\
    exists n3,
    edge n1 n3 /\
    reachable n3 n2.

  #[export] Hint Unfold owns : main.

  (* *Containment* is the reflexive transitive closure of ownership. *)

  Definition contains := clos_refl_trans owns.

  #[export] Hint Unfold contains : main.

  (* Every node should be owned by its owner. *)

  Axiom soundness : forall n, owns (owner n) n.

  (* The egress from a node summarizes the egress from the nodes it owns. *)

  Axiom reflection :
    forall n1 n2 n3,
    owns n1 n2 ->
    edge n2 n3 ->
    exists n4,
    edge n1 n4 /\
    contains n4 n3.

  #[export] Hint Resolve reflection : main.

  (* Let there be a *root* node which contains every node. *)

  Parameter root : node.

  Axiom rootedness : forall n, contains root n.

  #[export] Hint Resolve rootedness : main.
End Overtree.

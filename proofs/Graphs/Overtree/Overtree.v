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

  (* Each node is associated with a node called its *parent*. *)

  Parameter parent : node -> node.

  (* Each node is reachable from its parent via a path through its siblings. *)

  Axiom connectedness :
    forall n,
    clos_refl_trans (
      fun n1 n2 => edge n1 n2 /\ parent n2 = parent n
    ) (parent n) n.

  #[export] Hint Resolve connectedness : main.

  (* Ancestorship is the reflexive transitive closure of parenthood. *)

  Definition ancestor := clos_refl_trans (fun n1 n2 => n1 = parent n2).

  #[export] Hint Unfold ancestor : main.

  (* Ancestorship is antisymmetric. *)

  Axiom ancestorshipAntisymmetry :
    forall n1 n2, ancestor n1 n2 -> ancestor n2 n1 -> n1 = n2.

  #[export] Hint Resolve ancestorshipAntisymmetry : main.

  (* There is a *root* node which is an ancestor for every node. *)

  Parameter root : node.

  Axiom rootedness : forall n, ancestor root n.

  #[export] Hint Resolve rootedness : main.
End Overtree.

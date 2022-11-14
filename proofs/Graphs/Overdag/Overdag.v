(**********************)
(**********************)
(****              ****)
(****   Overdags   ****)
(****              ****)
(**********************)
(**********************)

Require Import Coq.Relations.Relation_Operators.

Module Type Overdag.
  #[local] Arguments clos_refl_trans {A} _ _ _.

  (* An *overdag* has a set of nodes, just like any graph. *)

  Parameter node : Type.

  (* Edges are directed in our formulation, but this is inessential. *)

  Parameter edge : node -> node -> Prop.

  (* Each node is associated with a set of nodes called its *parents*. *)

  Parameter parent : node -> node -> Prop.

  (* Each node is reachable from its parents via paths through its siblings. *)

  Axiom connectedness :
    forall p n,
    parent p n ->
    clos_refl_trans (fun n1 n2 => edge n1 n2 /\ parent p n2) p n.

  #[export] Hint Resolve connectedness : main.

  (* Ancestorship is the reflexive transitive closure of parenthood. *)

  Definition ancestor := clos_refl_trans parent.

  #[export] Hint Unfold ancestor : main.

  (* Ancestorship is antisymmetric. *)

  Axiom ancestorshipAntisymmetry :
    forall n1 n2, ancestor n1 n2 -> ancestor n2 n1 -> n1 = n2.

  #[export] Hint Resolve ancestorshipAntisymmetry : main.

  (* There is a *root* node which is an ancestor of every node. *)

  Parameter root : node.

  Axiom rootedness : forall n, ancestor root n.

  #[export] Hint Resolve rootedness : main.
End Overdag.

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

  (*
    Each node is also associated with a set of *member* nodes. That node is
    called a proxy for its members.
  *)

  Parameter member : node -> node -> Prop.

  (*
    Every node is reachable from all of its proxies via paths through other
    members of those proxies.
  *)

  Axiom connectedness :
    forall p n,
    member p n ->
    clos_refl_trans (fun n1 n2 => edge n1 n2 /\ member p n2) p n.

  #[export] Hint Resolve connectedness : main.

  (* Ancestorship is the reflexive transitive closure of membership. *)

  Definition ancestor := clos_refl_trans member.

  #[export] Hint Unfold ancestor : main.

  (* Ancestorship is antisymmetric. *)

  Axiom ancestorshipAntisymmetry :
    forall n1 n2, ancestor n1 n2 -> ancestor n2 n1 -> n1 = n2.

  #[export] Hint Resolve ancestorshipAntisymmetry : main.

  (* There is a *root* node which is an ancestor for every node. *)

  Parameter root : node.

  Axiom rootedness : forall n, ancestor root n.

  #[export] Hint Resolve rootedness : main.
End Overdag.

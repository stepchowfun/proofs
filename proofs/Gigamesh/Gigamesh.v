(************************)
(************************)
(****                ****)
(****   Gigameshes   ****)
(****                ****)
(************************)
(************************)

Require Import Coq.Relations.Relation_Operators.

Module Type Gigamesh.
  #[local] Arguments clos_refl_trans {A} _ _ _.

  (* A *gigamesh* has a set of nodes, just like any graph. *)

  Parameter node : Type.

  (* Pairs of nodes may be related via directed *edges*. *)

  Parameter edge : node -> node -> Prop.

  (* Pairs of nodes may also be related via *parent-child* relationships. *)

  Parameter parent : node -> node -> Prop.

  (* *Ancestorship* is the reflexive transitive closure of parenthood. *)

  Definition ancestor := clos_refl_trans parent.

  #[export] Hint Unfold ancestor : main.

  (* Ancestorship is antisymmetric and thus a partial order. *)

  Axiom antisymmetry :
    forall n1 n2, ancestor n1 n2 -> ancestor n2 n1 -> n1 = n2.

  #[export] Hint Resolve antisymmetry : main.

  (*
    An edge from one node to another is *admitted* if some ancestor of the
    source is a parent of some descendant of the target. In other words,
    parenthood grants descendants of the parent access to ancestors of the
    child.
  *)

  Definition admitted n1 n2 :=
    exists n3 n4, ancestor n3 n1 /\ parent n3 n4 /\ ancestor n2 n4.

  #[export] Hint Unfold admitted : main.

  (* Every edge is admitted. *)

  Axiom admission : forall n1 n2, edge n1 n2 -> admitted n1 n2.

  #[export] Hint Resolve admission : main.
End Gigamesh.

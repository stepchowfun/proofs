(**********************************)
(**********************************)
(****                          ****)
(****   Admissibility graphs   ****)
(****                          ****)
(**********************************)
(**********************************)

Require Import Coq.Relations.Relation_Operators.

Module Type AdmissibilityGraph.
  #[local] Arguments clos_trans {A} _ _ _.

  (* A *admissibility graph* has a set of nodes, just like any graph. *)

  Parameter node : Type.

  (* Nodes may *depend on* each other. *)

  Parameter dependency : node -> node -> Prop.

  (* Nodes may also be related via *parent-child* relationships. *)

  Parameter parent : node -> node -> Prop.

  (* *Ancestorship* is the reflexive transitive closure of parenthood. *)

  Definition ancestor := clos_trans parent.

  #[export] Hint Unfold ancestor : main.

  (*
    A dependency on a target by a source is *admissible* if some ancestor of
    the source is a parent of some descendant of the target. In other words,
    descendants of a node may depend on ancestors of the children of that node.
  *)

  Definition admissible n1 n2 :=
    exists n3 n4, ancestor n3 n1 /\ parent n3 n4 /\ ancestor n2 n4.

  #[export] Hint Unfold admissible : main.

  (* Parenthood is reflexive. *)

  Axiom reflexivity : forall n, parent n n.

  #[export] Hint Resolve reflexivity : main.

  (* Ancestorship is antisymmetric and thus a partial order. *)

  Axiom antisymmetry :
    forall n1 n2, ancestor n1 n2 -> ancestor n2 n1 -> n1 = n2.

  #[export] Hint Resolve antisymmetry : main.

  (* Every dependency is admissible. *)

  Axiom admissibility : forall n1 n2, dependency n1 n2 -> admissible n1 n2.

  #[export] Hint Resolve admissibility : main.
End AdmissibilityGraph.

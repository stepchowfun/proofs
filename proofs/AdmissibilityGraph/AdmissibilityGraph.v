(**********************************)
(**********************************)
(****                          ****)
(****   Admissibility graphs   ****)
(****                          ****)
(**********************************)
(**********************************)

Require Import Coq.Relations.Relation_Operators.

Module Type AdmissibilityGraph.
  #[local] Arguments clos_refl_trans {A} _ _ _.

  (* A *admissibility graph* has a set of nodes, just like any graph. *)

  Parameter node : Type.

  (* Pairs of nodes may be related via edges called *references*. *)

  Parameter reference : node -> node -> Prop.

  (* Pairs of nodes may also be related via *parent-child* relationships. *)

  Parameter parent : node -> node -> Prop.

  (* *Ancestorship* is the reflexive transitive closure of parenthood. *)

  Definition ancestor := clos_refl_trans parent.

  #[export] Hint Unfold ancestor : main.

  (*
    An reference from one node to another is *admissible* if some ancestor of
    the source is a parent of some descendant of the target. In other words,
    descendants of a node may reference ancestors of the children of that node.
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

  (* Every reference is admissible. *)

  Axiom admissibility : forall n1 n2, reference n1 n2 -> admissible n1 n2.

  #[export] Hint Resolve admissibility : main.
End AdmissibilityGraph.

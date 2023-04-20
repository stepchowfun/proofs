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

  (* Nodes are related via *child-parent* relationships. *)

  Parameter parent : node -> node -> Prop.

  (* Parenthood is reflexive. *)

  Axiom reflexivity : forall n, parent n n.

  #[export] Hint Resolve reflexivity : main.

  (* *Ancestorship* is the reflexive transitive closure of parenthood. *)

  Definition ancestor := clos_trans parent.

  #[export] Hint Unfold ancestor : main.

  (*
    A dependency on a target by a source is *admissible* if some ancestor of
    the source is a parent of some descendant of the target.
  *)

  Definition admissible n1 n2 :=
    exists n3 n4, ancestor n1 n3 /\ parent n4 n3 /\ ancestor n4 n2.

  #[export] Hint Unfold admissible : main.
End AdmissibilityGraph.

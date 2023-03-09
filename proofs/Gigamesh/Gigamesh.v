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

  (* Each node is associated with a node called its *parent*. *)

  Parameter parent : node -> node.

  (* *Ancestorship* is the reflexive transitive closure of parenthood. *)

  Definition ancestor := clos_refl_trans (fun n1 n2 => n1 = parent n2).

  #[export] Hint Unfold ancestor : main.

  (* Ancestorship is antisymmetric and thus a partial order. *)

  Axiom antisymmetry :
    forall n1 n2, ancestor n1 n2 -> ancestor n2 n1 -> n1 = n2.

  #[export] Hint Resolve antisymmetry : main.

  (*
    Every node is reachable from its parent via a path through the descendants
    of that parent.
  *)

  Axiom connectedness :
    forall n,
    let p := parent n
    in clos_refl_trans (fun n1 n2 => edge n1 n2 /\ ancestor p n2) p n.

  #[export] Hint Resolve connectedness : main.

  (* For every edge, the parent of the target is an ancestor of the source. *)

  Axiom encapsulation : forall n1 n2, edge n1 n2 -> ancestor (parent n2) n1.

  #[export] Hint Resolve encapsulation : main.
End Gigamesh.

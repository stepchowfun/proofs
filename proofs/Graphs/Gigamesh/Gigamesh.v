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

  (* There is a distinguished *root* node. *)

  Parameter root : node.

  (* Pairs of nodes may be related via directed edges. *)

  Parameter edge : node -> node -> Prop.

  (* Each node is associated with a set of nodes called its *parents*. *)

  Parameter parent : node -> node -> Prop.

  (* *Ancestorship* is the reflexive transitive closure of parenthood. *)

  Definition ancestor := clos_refl_trans parent.

  #[export] Hint Unfold ancestor : main.

  (* Each node is reachable from its parents via paths through its siblings. *)

  Axiom connectedness :
    forall p n,
    parent p n ->
    clos_refl_trans (fun n1 n2 => edge n1 n2 /\ parent p n2) p n.

  #[export] Hint Resolve connectedness : main.

  (* For every edge, some ancestor of the source is a parent of the target. *)

  Axiom encapsulation :
    forall n1 n2, edge n1 n2 -> exists p, ancestor p n1 /\ parent p n2.

  #[export] Hint Resolve encapsulation : main.

  (* Ancestorship is antisymmetric and thus a partial order. *)

  Axiom antisymmetry :
    forall n1 n2, ancestor n1 n2 -> ancestor n2 n1 -> n1 = n2.

  #[export] Hint Resolve antisymmetry : main.

  (* The root is an ancestor of every node. *)

  Axiom rootedness : forall n, ancestor root n.

  #[export] Hint Resolve rootedness : main.
End Gigamesh.
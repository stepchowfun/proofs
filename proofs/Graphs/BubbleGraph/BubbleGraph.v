(***************************)
(***************************)
(****                   ****)
(****   Bubble graphs   ****)
(****                   ****)
(***************************)
(***************************)

Require Import Coq.Relations.Relation_Operators.

Module Type BubbleGraph.
  #[local] Arguments clos_refl_trans {A} _ _ _.

  (* An *bubble graph* has a set of nodes, just like any graph. *)

  Parameter node : Type.

  (* Edges are directed in our formulation, but this is inessential. *)

  Parameter edge : node -> node -> Prop.

  (* A bubble graph also has a set of *bubbles*. *)

  Parameter bubble : Type.

  (* Each bubble is associated with a *root* node. *)

  Parameter root : bubble -> node.

  (* Each bubble is also associated with a set of *member* nodes. *)

  Parameter member : bubble -> node -> Prop.

  (*
    Every node in a bubble is reachable from the root of the bubble without
    leaving the bubble.
  *)

  Axiom connectedness :
    forall b n,
    member b n ->
    clos_refl_trans (fun n1 n2 => edge n1 n2 /\ member b n2) (root b) n.

  #[export] Hint Resolve connectedness : main.

  (* Let there be a *universe* bubble which contains the entire graph. *)

  Parameter universe : bubble.

  Axiom universality : forall n, member universe n.

  #[export] Hint Resolve universality : main.
End BubbleGraph.

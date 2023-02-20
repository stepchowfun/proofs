(******************************)
(******************************)
(****                      ****)
(****   VisibilityGraphs   ****)
(****                      ****)
(******************************)
(******************************)

Require Import Coq.Relations.Relation_Operators.

Module Type VisibilityGraph.
  #[local] Arguments clos_refl_trans {A} _ _ _.

  (* An *visibility graph* has a set of nodes, just like any graph. *)

  Parameter node : Type.

  (* Edges are directed in our formulation, but this is inessential. *)

  Parameter edge : node -> node -> Prop.

  (* Each node is associated with a set of nodes called its *parents*. *)

  Parameter parent : node -> node -> Prop.

  (*
    *Reachability* is the reflexive transitive closure of the edge relation.
  *)

  Definition reachable := clos_refl_trans edge.

  #[export] Hint Unfold reachable : main.

  (* Every node is reachable from all its parents. *)

  Axiom reachability : forall n1 n2, parent n1 n2 -> reachable n1 n2.

  #[export] Hint Resolve reachability : main.

  (* Ingress to a node must traverse a parent of that node. *)

  Axiom visibility :
    forall n1 n2 n3, edge n1 n2 -> reachable n2 n3 ->
    exists n4, parent n4 n3 /\ (reachable n4 n1 \/ reachable n2 n4).

  #[export] Hint Resolve visibility : main.
End VisibilityGraph.

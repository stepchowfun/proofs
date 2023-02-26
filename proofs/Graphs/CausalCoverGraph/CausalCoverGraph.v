(*********************************)
(*********************************)
(****                         ****)
(****   Causal cover graphs   ****)
(****                         ****)
(*********************************)
(*********************************)

Require Import Coq.Relations.Relation_Operators.

Module Type CausalCoverGraph.
  #[local] Arguments clos_refl_trans {A} _ _ _.

  (* The nodes of a *causal cover graph* represent events in spacetime. *)

  Parameter event : Type.

  (*
    The edges of the graph represent indivisible timelike or lightlike curves
    and thus indicate direct *causality* between events. Unless otherwise
    specified, closed timelike curves are allowed.
  *)

  Parameter causes : event -> event -> Prop.

  (*
    An event causally *precedes* another if the events are related by the
    reflexive transitive closure of the direct causality relation. In physical
    terms, this occurs when the former event is connected to the latter by a
    timelike or lightlike curve, which itself may be the concatenation of
    shorter curves.
  *)

  Definition precedes := clos_refl_trans causes.

  #[export] Hint Unfold precedes : main.

  (*
    Each event is associated with a set of events called its causal *cover*.
    The meaning of the causal cover will be made precise below. Informally, a
    causal cover of an event is a convex hypersurface in spacetime that
    truncates the past light cone of that event.
  *)

  Parameter cover : event -> event -> Prop.

  (*
    Members of a causal cover must not be causally related. Informally, the
    spacetime hypersurface represented by the cover must be convex.
  *)

  Axiom coverConvexity :
    forall e1 e2 e3,
    cover e1 e3 ->
    cover e2 e3 ->
    precedes e1 e2 ->
    e1 = e2.

  #[export] Hint Resolve coverConvexity : main.

  (*
    An event must be preceded by every member of its causal cover. Informally,
    the spacetime hypersurface represented by the cover of an event must be
    contained within the past light cone of that event.
  *)

  Axiom coverBoundedness : forall e1 e2, cover e1 e2 -> precedes e1 e2.

  #[export] Hint Resolve coverBoundedness : main.

  (*
    Every event along a timelike or lightlike curve must be causally related to
    some member of the cover of the endpoint of the curve. Informally, the
    spacetime hypersurface represented by the cover must have no holes through
    which timelike or lightlike curves may pass without intersecting the
    surface.
  *)

  Axiom coverConnectedness :
    forall e1 e2 e3, causes e1 e2 -> precedes e2 e3 ->
    exists n4, cover n4 e3 /\ (precedes n4 e1 \/ precedes e2 n4).

  #[export] Hint Resolve coverConnectedness : main.
End CausalCoverGraph.

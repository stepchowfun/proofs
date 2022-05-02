Require Import Main.ContextGraph.ContextGraph.
Require Import Main.Tactics.

Module TrivialContextGraph <: ContextGraph.
  Definition node := unit.

  Definition edge (x y z : node) := False.

  (* Coq requires that we copy this verbatim from `ContextGraph`. *)
  Inductive horizontallyReachable
    (context : node) (start : node) : node -> Prop :=
  | horizontalReflexivity :
    horizontallyReachable context start start
  | horizontalExtension :
    forall source target,
    horizontallyReachable context start source ->
    edge context source target ->
    horizontallyReachable context start target.

  #[local] Hint Constructors horizontallyReachable : main.

  (* Coq requires that we copy this verbatim from `ContextGraph`. *)
  Definition rooted context := horizontallyReachable context context.

  (* Coq requires that we copy this verbatim from `ContextGraph`. *)
  Inductive verticallyReachable (start : node) : node -> Prop :=
  | verticalReflexivity :
    verticallyReachable start start
  | verticalExtension :
    forall context node,
    verticallyReachable start context ->
    rooted context node ->
    verticallyReachable start node.

  #[local] Hint Constructors verticallyReachable : main.

  Theorem verticalAntisymmetry :
    forall node1 node2,
    verticallyReachable node1 node2 ->
    verticallyReachable node2 node1 ->
    node1 = node2.
  Proof.
    clean.
    elim node1.
    elim node2.
    magic.
  Qed.

  Theorem sourcesRooted :
    forall context source target,
    edge context source target ->
    rooted context source.
  Proof.
    magic.
  Qed.

  Definition origin := tt.

  Theorem originality : forall node, verticallyReachable origin node.
  Proof.
    clean.
    elim origin.
    elim node0.
    magic.
  Qed.
End TrivialContextGraph.

Module TrivialContextGraphTheorems := ContextGraphTheorems TrivialContextGraph.

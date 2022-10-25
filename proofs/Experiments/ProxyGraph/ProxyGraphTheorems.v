(*****************************************)
(*****************************************)
(****                                 ****)
(****   Theorems about proxy graphs   ****)
(****                                 ****)
(*****************************************)
(*****************************************)

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.
Require Import Main.Experiments.ProxyGraph.ProxyGraph.
Require Import Main.Tactics.

Module ProxyGraphTheorems (Graph : ProxyGraph).
  Import Graph.

  #[local] Arguments clos_refl_trans {A} _ _ _.
  #[local] Hint Constructors clos_refl_trans : main.

  (* The only node that can vertically reach the root is itself. *)

  Theorem rootUniquelyReachable :
    forall n,
    verticallyReachable n root ->
    n = root.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve rootUniquelyReachable : main.

  (* The root is the only node which can vertically reach every other node. *)

  Theorem rootReachUniqueness :
    forall n1,
    (forall n2, verticallyReachable n1 n2) ->
    n1 = root.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve rootReachUniqueness : main.

  (*
    *Reachability* is the reflexive transitive closure of the edge relation.
  *)

  Definition reachable := clos_refl_trans edge.

  #[export] Hint Unfold reachable : main.

  (* Horizontal reachability implies reachability. *)

  Theorem horizontalSoundness :
    forall n1 n2 n3,
    horizontallyReachable n1 n2 n3 ->
    reachable n2 n3.
  Proof.
    clean.
    induction H; eSearch.
  Qed.

  #[export] Hint Resolve horizontalSoundness : main.

  (* Vertical reachability implies reachability. *)

  Theorem verticalSoundness :
    forall n1 n2,
    verticallyReachable n1 n2 ->
    reachable n1 n2.
  Proof.
    clean.
    induction H; eSearch.
  Qed.

  #[export] Hint Resolve verticalSoundness : main.
End ProxyGraphTheorems.

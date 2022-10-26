(*******************************************)
(*******************************************)
(****                                   ****)
(****   Theorems about context graphs   ****)
(****                                   ****)
(*******************************************)
(*******************************************)

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.
Require Import Main.ContextGraph.ContextGraph.
Require Import Main.Tactics.

Module ContextGraphTheorems (Graph : ContextGraph).
  Import Graph.

  #[local] Arguments clos_refl_trans {A} _ _ _.
  #[local] Hint Constructors clos_refl_trans : main.

  (* The root only appears in the root context. *)

  Theorem rootContextLeft : forall c n, edge c root n -> c = root.
  Proof.
    eSearch.
  Qed.

  #[export] Hint Resolve rootContextLeft : main.


  Theorem rootContextRight : forall c n, edge c n root -> c = root.
  Proof.
    clean.
    pose proof (connectedness c n root H).
    assert (contains c root); eSearch.
  Qed.

  #[export] Hint Resolve rootContextRight : main.

  (* The only node that can vertically reach the root is itself. *)

  Theorem rootUniquelyReachable :
    forall n,
    verticallyReachable n root ->
    n = root.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve rootUniquelyReachable : main.

  (*
    *Reachability* is the reflexive transitive closure of the edge relation
    existentially quantified over the context.
  *)

  Definition reachable := clos_refl_trans (
    fun n1 n2 => exists n3, edge n3 n1 n2
  ).

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
End ContextGraphTheorems.

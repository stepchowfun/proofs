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

  (* Every node in a context has a loop. *)

  Theorem reflexivity : forall c n, contains c n -> edge c n n.
  Proof.
    eSearch.
  Qed.

  #[export] Hint Resolve reflexivity : main.

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
    assert (contains c root); [eSearch | search].
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
End ContextGraphTheorems.

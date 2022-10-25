(***********************************************)
(***********************************************)
(****                                       ****)
(****   The simplest possible proxy graph   ****)
(****                                       ****)
(***********************************************)
(***********************************************)

Require Import Coq.Relations.Relation_Operators.
Require Import Main.Experiments.ProxyGraph.ProxyGraph.
Require Import Main.Experiments.ProxyGraph.ProxyGraphTheorems.
Require Import Main.Tactics.

Module TrivialProxyGraph <: ProxyGraph.
  #[local] Arguments clos_refl_trans {A} _ _ _.
  #[local] Hint Resolve rt_refl : main.

  Definition node := unit.

  #[export] Hint Unfold node : main.

  Definition edge (n1 n2 : node) := False.

  #[export] Hint Unfold edge : main.

  Definition proxy (p n : node) := False.

  #[export] Hint Unfold proxy : main.

  (* Coq requires that we copy this verbatim from `ProxyGraph`. *)
  Definition horizontallyReachable p := clos_refl_trans (
    fun n1 n2 => edge n1 n2 /\ proxy p n2
  ).

  #[export] Hint Unfold horizontallyReachable : main.

  (* Coq requires that we copy this verbatim from `ProxyGraph`. *)
  Definition proxies p := horizontallyReachable p p.

  #[export] Hint Unfold proxies : main.

  (* Coq requires that we copy this verbatim from `ProxyGraph`. *)
  Definition verticallyReachable := clos_refl_trans proxies.

  #[export] Hint Unfold verticallyReachable : main.

  Theorem proxySoundness : forall p n, proxy p n -> proxies p n.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve proxySoundness : main.

  Theorem verticalAntisymmetry :
    forall n1 n2,
    verticallyReachable n1 n2 ->
    verticallyReachable n2 n1 ->
    n1 = n2.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve verticalAntisymmetry : main.

  Definition root := tt.

  #[export] Hint Unfold root : main.

  Theorem rootReach : forall n, verticallyReachable root n.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve rootReach : main.
End TrivialProxyGraph.

Module TrivialProxyGraphTheorems := ProxyGraphTheorems TrivialProxyGraph.

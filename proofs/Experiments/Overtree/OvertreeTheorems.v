(**************************************)
(**************************************)
(****                              ****)
(****   Theorems about overtrees   ****)
(****                              ****)
(**************************************)
(**************************************)

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.
Require Import Main.Experiments.Overtree.Overtree.
Require Import Main.Tactics.

Module OvertreeTheorems (Graph : Overtree).
  Import Graph.

  #[local] Arguments clos_refl_trans {A} _ _ _.
  #[local] Arguments clos_refl_trans_1n {A} _ _ _.
  #[local] Arguments clos_refl_trans_n1 {A} _ _ _.
  #[local] Hint Constructors clos_refl_trans : main.
  #[local] Hint Constructors clos_refl_trans_1n : main.
  #[local] Hint Constructors clos_refl_trans_n1 : main.
  #[local] Hint Resolve clos_rt1n_rt : main.
  #[local] Hint Resolve clos_rt_rt1n : main.
  #[local] Hint Resolve clos_rtn1_rt : main.
  #[local] Hint Resolve clos_rt_rtn1 : main.

  (* The only node that can vertically reach the root is itself. *)

  Theorem rootUniquelyReachable :
    forall n,
    verticallyReachable n root ->
    n = root.
  Proof.
    clean.
    assert (clos_refl_trans_n1 proxies n root); search.
    pose proof rootProxy.
    induction H0; search.
    assert (y = z); search.
  Qed.

  #[export] Hint Resolve rootUniquelyReachable : main.

  (* The root is the only node which is its own proxy. *)

  Theorem rootProxyUniqueness : forall n, proxy n = n -> n = root.
  Proof.
    clean.
    induction (rootReach n); search.
  Qed.

  #[export] Hint Resolve rootProxyUniqueness : main.

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
    forall n1 n2,
    horizontallyReachable n1 n2 ->
    reachable n1 n2.
  Proof.
    clean.
    induction H; eSearch.
  Qed.

  #[export] Hint Resolve horizontalSoundness : main.

  (*
    If a node is horizontally reachable from another node, they share a proxy.
  *)

  Theorem horizontalCovalency :
    forall n1 n2,
    horizontallyReachable n1 n2 ->
    proxy n1 = proxy n2.
  Proof.
    clean.
    induction H; search.
  Qed.

  #[export] Hint Resolve horizontalCovalency : main.

  (* The proxy for a given node is unique. *)

  Theorem proxyUniqueness :
    forall n1 n2 n3,
    proxies n1 n3 ->
    proxies n2 n3 ->
    n1 = n2.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve proxyUniqueness : main.

  (* Every node is proxied by its proxy. *)

  Theorem proxySoundness : forall n, proxies (proxy n) n.
  Proof.
    clean.
    assert (clos_refl_trans_n1 proxies root n).
    - apply clos_rt_rtn1.
      apply rootReach.
    - invert H.
      + split; eSearch.
      + invert H0.
        search.
  Qed.

  #[export] Hint Resolve proxySoundness : main.

  (* Every node must be vertically reachable from its proxy. *)

  Theorem verticalProxyReach : forall n, verticallyReachable (proxy n) n.
  Proof.
    search.
  Qed.

  #[export] Hint Resolve verticalProxyReach : main.

  (* Vertical reachability implies reachability. *)

  Theorem verticalSoundness :
    forall n1 n2,
    verticallyReachable n1 n2 ->
    reachable n1 n2.
  Proof.
    clean.
    induction H; eSearch.
    invert H.
    invert H1.
    apply rt_trans with (y := x); search.
    apply horizontalSoundness.
    search.
  Qed.

  #[export] Hint Resolve verticalSoundness : main.

  (* Vertical reachability is antisymmetric and thus a partial order. *)

  Theorem verticalAntisymmetry :
    forall n1 n2,
    verticallyReachable n1 n2 ->
    verticallyReachable n2 n1 ->
    n1 = n2.
  Proof.
    clean.
    assert (n1 <> n2 -> verticallyReachable n2 root).
    - assert (clos_refl_trans_1n proxies root n1).
      + apply clos_rt_rt1n.
        apply rootReach.
      + induction H1; search.
        clean.
        assert (clos_refl_trans_n1 proxies n2 y); search.
        destruct H4; eSearch.
        assert (clos_refl_trans_n1 proxies z n2); search.
        destruct H4; eSearch.
    - destruct (classic (n1 = n2)); search.
      pose proof (rootUniquelyReachable n2).
      search.
  Qed.

  #[export] Hint Resolve verticalAntisymmetry : main.

  (* The nodes which can vertically reach a given node are totally ordered. *)

  Theorem verticalAncestorsTotallyOrdered :
    forall n1 n2 n3,
    verticallyReachable n1 n3 ->
    verticallyReachable n2 n3 ->
    verticallyReachable n1 n2 \/
    verticallyReachable n2 n1.
  Proof.
    clean.
    assert (clos_refl_trans_n1 proxies n1 n3); search.
    induction H1; search.
    assert (clos_refl_trans_n1 proxies n2 z); search.
    destruct H3; search.
  Qed.

  #[export] Hint Resolve verticalAncestorsTotallyOrdered : main.

End OvertreeTheorems.

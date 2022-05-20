(***********************)
(***********************)
(****               ****)
(****   Overtrees   ****)
(****               ****)
(***********************)
(***********************)

Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.
Require Import Main.Tactics.

Module Type Overtree.
  #[local] Arguments clos_refl_trans {A} _ _ _.

  (* An *overtree* has a set of nodes, just like any graph. *)

  Parameter node : Type.

  (* Edges are directed in our formulation, but this is inessential. *)

  Parameter edge : node -> node -> Prop.

  (* Each node is associated with a node called its *proxy*. *)

  Parameter proxy : node -> node.

  (* An edge is called *covalent* if its source and target share a proxy. *)

  Definition covalent n1 n2 := edge n1 n2 /\ proxy n1 = proxy n2.

  (*
    *Horizontal reachability* is the transitive reflexive closure of covalency.
  *)

  Definition horizontallyReachable := clos_refl_trans covalent.

  (*
    A node *proxies* another node if it's the proxy for that node and that node
    is horizontally reachable from one of the proxy's neighbors.
  *)

  Definition proxies n1 n2 :=
    proxy n2 = n1 /\
    exists n3,
    edge n1 n3 /\
    horizontallyReachable n3 n2.

  (*
    *Vertical reachability* is the transitive reflexive closure of proxying.
  *)

  Definition verticallyReachable := clos_refl_trans proxies.

  (*
    Let there be a *root* node which has a loop, which is its own proxy, and
    from which every node is vertically reachable.
  *)

  Parameter root : node.

  Axiom rootLoop : edge root root.

  Axiom rootProxy : proxy root = root.

  Axiom rootReach : forall n, verticallyReachable root n.
End Overtree.

Module OvertreeTheorems (Graph : Overtree).
  Import Graph.

  #[local] Arguments clos_refl_trans {A} _ _ _.

  #[local] Arguments clos_refl_trans_1n {A} _ _ _.

  #[local] Arguments clos_refl_trans_n1 {A} _ _ _.

  (* The only node that can vertically reach the root is itself. *)

  Theorem rootUniquelyReachable :
    forall n,
    verticallyReachable n root ->
    n = root.
  Proof.
    clean.
    assert (clos_refl_trans_n1 proxies n root).
    - apply clos_rt_rtn1.
      magic.
    - clear H.
      fact rootProxy.
      induction H0; magic.
      assert (y = z).
      + destruct H0.
        magic.
      + magic.
  Qed.

  #[export] Hint Resolve rootUniquelyReachable : main.

  (* The root is the only node which is its own proxy. *)

  Theorem rootProxyUniqueness : forall n, proxy n = n -> n = root.
  Proof.
    clean.
    induction (rootReach n); magic.
    destruct H0.
    magic.
  Qed.

  #[export] Hint Resolve rootProxyUniqueness : main.

  (* The root is the only node which can vertically reach every other node. *)

  Theorem rootReachUniqueness :
    forall n1,
    (forall n2, verticallyReachable n1 n2) ->
    n1 = root.
  Proof.
    magic.
  Qed.

  #[export] Hint Resolve rootReachUniqueness : main.

  (*
    *Reachability* is the transitive reflexive closure of the edge relation.
  *)

  Definition reachable := clos_refl_trans edge.

  (* Horizontal reachability implies reachability. *)

  Theorem horizontalSoundness :
    forall n1 n2,
    horizontallyReachable n1 n2 ->
    reachable n1 n2.
  Proof.
    clean.
    induction H.
    - apply rt_step.
      destruct H.
      magic.
    - apply rt_refl.
    - apply rt_trans with (y := y); magic.
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
    induction H; magic.
    destruct H.
    magic.
  Qed.

  #[export] Hint Resolve horizontalCovalency : main.

  (* The proxy for a given node is unique. *)

  Theorem proxyUniqueness :
    forall n1 n2 n3,
    proxies n1 n3 ->
    proxies n2 n3 ->
    n1 = n2.
  Proof.
    unfold proxies.
    magic.
  Qed.

  #[export] Hint Resolve proxyUniqueness : main.

  (* Every node is proxied by its proxy. *)

  Theorem proxySoundness : forall n, proxies (proxy n) n.
  Proof.
    clean.
    assert (clos_refl_trans_n1 proxies root n).
    - apply clos_rt_rtn1. apply rootReach.
    - invert H.
      + split.
        * magic.
        * {
          exists root.
          split.
          - rewrite rootProxy.
            apply rootLoop.
          - apply rt_refl.
        }
      + invert H0.
        unfold proxies; magic.
  Qed.

  #[export] Hint Resolve proxySoundness : main.

  (* Every node must be vertically reachable from its proxy. *)

  Theorem verticalProxyReach : forall n, verticallyReachable (proxy n) n.
  Proof.
    clean.
    apply rt_step.
    magic.
  Qed.

  #[export] Hint Resolve verticalProxyReach : main.

  (* Vertical reachability implies reachability. *)

  Theorem verticalSoundness :
    forall n1 n2,
    verticallyReachable n1 n2 ->
    reachable n1 n2.
  Proof.
    clean.
    induction H.
    - invert H.
      invert H1.
      apply rt_trans with (y := x).
      + apply rt_step.
        magic.
      + apply horizontalSoundness.
        magic.
    - apply rt_refl.
    - apply rt_trans with (y := y); magic.
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
      + induction H1; magic.
        clean.
        assert (clos_refl_trans_n1 proxies n2 y).
        * apply clos_rt_rtn1.
          magic.
        * {
          destruct H4.
          - assert (clos_refl_trans_n1 proxies z n2).
            + apply clos_rt_rtn1.
              magic.
            + destruct H4; magic.
              assert (x = y).
              * apply proxyUniqueness with (n3 := z0); magic.
              * apply rt_trans with (y := z); magic.
                apply clos_rtn1_rt.
                magic.
          - assert (x = y).
            + apply proxyUniqueness with (n3 := z0); magic.
            + apply clos_rtn1_rt.
              magic.
        }
    - destruct (classic (n1 = n2)); magic.
      fact (rootUniquelyReachable n2).
      magic.
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
    assert (clos_refl_trans_n1 proxies n1 n3).
    - apply clos_rt_rtn1.
      magic.
    - induction H1; magic.
      assert (clos_refl_trans_n1 proxies n2 z).
      + apply clos_rt_rtn1.
        magic.
      + destruct H3; magic.
        apply IHclos_refl_trans_n1.
        * apply clos_rtn1_rt.
          magic.
        * unfold proxies in H1.
          unfold proxies in H3.
          apply clos_rtn1_rt.
          magic.
  Qed.

  #[export] Hint Resolve verticalAncestorsTotallyOrdered : main.

End OvertreeTheorems.

(**************************)
(**************************)
(****                  ****)
(****   Proxy graphs   ****)
(****                  ****)
(**************************)
(**************************)

Require Import Coq.Relations.Relation_Operators.

Module Type ProxyGraph.
  #[local] Arguments clos_refl_trans {A} _ _ _.

  (* An *proxy graph* has a set of nodes, just like any graph. *)

  Parameter node : Type.

  (* Edges are directed in our formulation, but this is inessential. *)

  Parameter edge : node -> node -> Prop.

  (*
    Each node can be a *proxy* for other nodes. Every node is associated with
    the subgraph induced by that node together with the nodes which have it as
    a proxy.
  *)

  Parameter proxy : node -> node -> Prop.

  (*
    *Horizontal reachability* for a proxy is the reflexive transitive closure
    of the edge relation restricted to edges for which the target node has that
    proxy.
  *)

  Definition horizontallyReachable p := clos_refl_trans (
    fun n1 n2 => edge n1 n2 /\ proxy p n2
  ).

  #[export] Hint Unfold horizontallyReachable : main.

  (*
    A node *proxies* another node iff it's a proxy for that node and that node
    is horizontally reachable for and from that proxy.
  *)

  Definition proxies p := horizontallyReachable p p.

  #[export] Hint Unfold proxies : main.

  (*
    *Vertical reachability* is the reflexive transitive closure of proxying.
  *)

  Definition verticallyReachable := clos_refl_trans proxies.

  #[export] Hint Unfold verticallyReachable : main.

  (* Each node is proxied by all its proxies. *)

  Axiom proxySoundness : forall p n, proxy p n -> proxies p n.

  #[export] Hint Resolve proxySoundness : main.

  (*
    Proxying is intended to signify nesting. To codify that intention, we
    require vertical reachability to be antisymmetric and thus a partial order.
  *)

  Axiom verticalAntisymmetry :
    forall n1 n2,
    verticallyReachable n1 n2 ->
    verticallyReachable n2 n1 ->
    n1 = n2.

  #[export] Hint Resolve verticalAntisymmetry : main.

  (*
    Let there be a *root* proxy from which every node is vertically reachable.
  *)

  Parameter root : node.

  Axiom rootReach : forall n, verticallyReachable root n.

  #[export] Hint Resolve rootReach : main.
End ProxyGraph.

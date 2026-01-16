(**********************************)
(**********************************)
(****                          ****)
(****   Admissibility graphs   ****)
(****                          ****)
(**********************************)
(**********************************)

Require Import Stdlib.Relations.Operators_Properties.
Require Import Stdlib.Relations.Relation_Operators.
Require Import main.tactics.

#[local] Arguments clos_refl_trans [A] _ _ _.
#[local] Arguments clos_refl_trans_1n [A] _ _ _.
#[local] Arguments clos_refl_trans_n1 [A] _ _ _.
#[local] Hint Constructors clos_refl_trans : main.
#[local] Hint Constructors clos_refl_trans_1n : main.
#[local] Hint Constructors clos_refl_trans_n1 : main.
#[local] Hint Resolve clos_rt1n_rt : main.
#[local] Hint Resolve clos_rt_rt1n : main.
#[local] Hint Resolve clos_rtn1_rt : main.
#[local] Hint Resolve clos_rt_rtn1 : main.

(*
  The *nodes* of an *admissibility graph* are related by two types of directed
  edges: *trusts* and *exports*.
*)

Record AdmissibilityGraph (Node : Type) := {
  Trusts : Node -> Node -> Prop;
  Exports : Node -> Node -> Prop;
}.

Arguments Trusts [_] _ _.
Arguments Exports [_] _ _.

(*
  The *transpose* of an admissibility graph is the result of swapping the edge
  types.
*)

Definition transpose [Node] (g : AdmissibilityGraph Node) :=
  {|
    Trusts := g.(Exports);
    Exports := g.(Trusts);
  |}.

Theorem transpose_involution Node (g : AdmissibilityGraph Node) :
  g = transpose (transpose g).
Proof.
  search.
Qed.

Hint Resolve transpose_involution : main.

(*
  If there is a (possibly empty) chain of trust from one node to another, we
  say the former is *trusting* of the latter. Likewise, if there is a (possibly
  empty) chain of exports from one node to another, we say the former is
  *exporting* the latter.
*)

Definition Trusting [Node] (g : AdmissibilityGraph Node) n1 n2 :=
  clos_refl_trans (Trusts g) n1 n2.

Definition Exporting [Node] (g : AdmissibilityGraph Node) n1 n2 :=
  clos_refl_trans (Exports g) n1 n2.

Theorem transpose_trusting Node (g : AdmissibilityGraph Node) :
  Trusting g = Exporting (transpose g).
Proof.
  assert (forall n1 n2, Trusting g n1 n2 = Exporting (transpose g) n1 n2);
    search.
Qed.

Hint Resolve transpose_trusting : main.

Theorem transpose_exporting Node (g : AdmissibilityGraph Node) :
  Exporting g = Trusting (transpose g).
Proof.
  assert (forall n1 n2, Exporting g n1 n2 = Trusting (transpose g) n1 n2);
    search.
Qed.

Hint Resolve transpose_trusting : main.

(*
  Every node can depend on itself, the nodes it trusts, the nodes that export
  it, any node that a node that trusts it can depend on, and any node that is
  exported by a node that it can depend on.
*)

Inductive Allowed [Node] (g : AdmissibilityGraph Node) (n : Node) : Node
  -> Prop :=
| loop : Allowed g n n
| trust : forall n1, Trusts g n n1 -> Allowed g n n1
| export : forall n1, Exports g n1 n -> Allowed g n n1
| egress : forall n1 n2, Trusts g n1 n -> Allowed g n1 n2 -> Allowed g n n2
| ingress : forall n1 n2, Exports g n1 n2 -> Allowed g n n1 -> Allowed g n n2.

Hint Constructors Allowed : main.

(*
  The dependencies allowed by the transpose of a graph are the flipped versions
  of the dependencies allowed by the original graph.
*)

Theorem duality Node (g : AdmissibilityGraph Node) n1 n2 :
  Allowed g n1 n2 <-> Allowed (transpose g) n2 n1.
Proof.
  split; clean; induction H; esearch.
Qed.

Hint Resolve duality : main.

(*
  If two admissibility graphs with the same nodes have corresponding edges
  between all pairs of *distinct* nodes, then they allow the same dependencies.
  In other words, nothing is gained by having a node trust or export itself.
*)

Theorem reflection Node (g1 g2 : AdmissibilityGraph Node) :
  (forall n1 n2, n1 = n2 \/ (Trusts g1 n1 n2 <-> Trusts g2 n1 n2)) ->
  (forall n1 n2, n1 = n2 \/ (Exports g1 n1 n2 <-> Exports g2 n1 n2)) ->
  forall n1 n2, Allowed g1 n1 n2 <-> Allowed g2 n1 n2.
Proof.
  split; clean; (
    induction H1; search; [
      specialize (H n n1) |
      specialize (H0 n1 n) |
      specialize (H n1 n) |
      specialize (H0 n1 n2)
    ]; esearch
  ).
Qed.

Hint Resolve reflection : main.

(* The following theorems generalize the egress and ingress axioms. *)

Theorem egress_extension Node (g : AdmissibilityGraph Node) n1 n2 n3 :
  Trusting g n1 n2 ->
  Allowed g n1 n3 ->
  Allowed g n2 n3.
Proof.
  clean.
  apply clos_rt_rtn1 in H.
  induction H; esearch.
Qed.

Hint Resolve egress_extension : main.

Theorem ingress_extension Node (g : AdmissibilityGraph Node) n1 n2 n3 :
  Exporting g n1 n2 ->
  Allowed g n3 n1 ->
  Allowed g n3 n2.
Proof.
  clean.
  apply clos_rt_rtn1 in H.
  induction H; esearch.
Qed.

Hint Resolve ingress_extension : main.

(*
  The following theorem gives an equivalent way to characterize which
  dependencies should be allowed.
*)

Theorem admission Node (g : AdmissibilityGraph Node) n1 n2 :
  Allowed g n1 n2 <->
  exists n3 n4,
    Trusting g n3 n1 /\
    Exporting g n4 n2 /\
    (n3 = n4 \/ Trusts g n3 n4 \/ Exports g n4 n3).
Proof.
  split; clean.
  - unfold Trusting, Exporting.
    induction H.
    + exists n, n.
      search.
    + exists n, n1.
      search.
    + exists n, n1.
      search.
    + destruct IHAllowed.
      destruct H1.
      exists x, x0.
      esearch.
    + destruct IHAllowed.
      destruct H1.
      exists x, x0.
      esearch.
  - apply egress_extension with (n1 := x); search.
    apply ingress_extension with (n1 := x0); search.
Qed.

Hint Resolve admission : main.

(*
  If a node trusts or exports another node, we say the former node is a
  *parent* of the latter and the latter is a child of the former.
*)

Definition ParentChild [Node] (g : AdmissibilityGraph Node) (n1 n2 : Node) :=
  Trusts g n1 n2 \/ Exports g n1 n2.

Theorem transpose_parent_child
  Node (g : AdmissibilityGraph Node) n1 n2
: ParentChild g n1 n2 <-> ParentChild (transpose g) n1 n2.
Proof.
  unfold ParentChild.
  search.
Qed.

Hint Resolve transpose_parent_child : main.

(*
  If there is a (possibly empty) chain of lineage from one node to another, we
  say the former is an *ancestor* of the latter and the latter is a
  *descendant* of the former. We omit the formal definition of the descendant
  relation in favor of consistently using the ancestor relation everywhere.
*)

Definition Ancestor [Node] (g : AdmissibilityGraph Node) n1 n2 :=
  clos_refl_trans (ParentChild g) n1 n2.

Theorem transpose_ancestor Node (g : AdmissibilityGraph Node) n1 n2 :
  Ancestor g n1 n2 <-> Ancestor (transpose g) n1 n2.
Proof.
  split; clean.
  - induction H; search.
    + apply rt_step.
      apply -> transpose_parent_child.
      search.
    + apply rt_trans with (y := y); search.
  - induction H; search.
    + apply rt_step.
      apply transpose_parent_child in H.
      search.
    + apply rt_trans with (y := y); search.
Qed.

Hint Resolve transpose_parent_child : main.

(* The ancestor relation is a superset of the trusting relation. *)

Theorem trusting_ancestor Node (g : AdmissibilityGraph Node) n1 n2 :
  Trusting g n1 n2 -> Ancestor g n1 n2.
Proof.
  clean.
  induction H; search.
  apply rt_trans with (y := y); search.
Qed.

Hint Resolve trusting_ancestor : main.

(* The ancestor relation is a superset of the exporting relation. *)

Theorem exporting_ancestor Node (g : AdmissibilityGraph Node) n1 n2 :
  Exporting g n1 n2 -> Ancestor g n1 n2.
Proof.
  clean.
  induction H; search.
  apply rt_trans with (y := y); search.
Qed.

Hint Resolve exporting_ancestor : main.

(* It may be desirable to require the ancestor relation to be antisymmetric. *)

Definition Antisymmetric [Node] (g : AdmissibilityGraph Node) :=
  forall n1 n2, Ancestor g n1 n2 -> Ancestor g n2 n1 -> n1 = n2.

(*
  A node is a *module* if it's an ancestor of every parent of every descendant
  of every child of the module.
*)

Definition Module [Node] (g : AdmissibilityGraph Node) n1 :=
  forall n2 n3 n4,
  ParentChild g n1 n2 ->
  ParentChild g n4 n3 ->
  Ancestor g n2 n3 ->
  Ancestor g n1 n4.

Theorem transpose_module Node (g : AdmissibilityGraph Node) n :
  Module g n <-> Module (transpose g) n.
Proof.
  unfold Module.
  split; clean.
  - apply -> transpose_ancestor.
    apply transpose_parent_child in H0.
    apply transpose_parent_child in H1.
    apply transpose_ancestor in H2.
    esearch.
  - apply transpose_ancestor.
    apply -> transpose_parent_child in H0.
    apply -> transpose_parent_child in H1.
    apply -> transpose_ancestor in H2.
    esearch.
Qed.

Hint Resolve transpose_module : main.

(*
  A node is *encapsulated* within a module if the module is an ancestor of the
  node and isn't exporting it. A node is *sandboxed* within a module if the
  module is an ancestor of the node and isn't trusting of it.
*)

Definition Encapsulated [Node] (g : AdmissibilityGraph Node) n1 n2 :=
  Module g n1 /\ Ancestor g n1 n2 /\ ~ Exporting g n1 n2.

Definition Sandboxed [Node] (g : AdmissibilityGraph Node) n1 n2 :=
  Module g n1 /\ Ancestor g n1 n2 /\ ~ Trusting g n1 n2.

Theorem transpose_encapsulated Node (g : AdmissibilityGraph Node) n1 n2 :
  Encapsulated g n1 n2 <-> Sandboxed (transpose g) n1 n2.
Proof.
  unfold Encapsulated, Sandboxed.
  split; clean.
  - repeat split; search.
    + apply -> transpose_module.
      search.
    + apply -> transpose_ancestor.
      search.
  - repeat split; search.
    + apply transpose_module.
      search.
    + apply transpose_ancestor.
      search.
Qed.

Hint Resolve transpose_encapsulated : main.

Theorem transpose_sandboxed Node (g : AdmissibilityGraph Node) n1 n2 :
  Sandboxed g n1 n2 <-> Encapsulated (transpose g) n1 n2.
Proof.
  unfold Encapsulated, Sandboxed.
  split; clean.
  - repeat split; search.
    + apply -> transpose_module.
      search.
    + apply -> transpose_ancestor.
      search.
  - repeat split; search.
    + apply transpose_module.
      search.
    + apply transpose_ancestor.
      search.
Qed.

Hint Resolve transpose_sandboxed : main.

(*
  The nodes which can depend on a node encapsulated within a module are
  descendants of the module.
*)

Theorem encapsulation Node (g : AdmissibilityGraph Node) n1 n2 n3 :
  Encapsulated g n1 n2 -> Allowed g n3 n2 -> Ancestor g n1 n3.
Proof.
  unfold Encapsulated.
  clean.
  apply admission in H0.
  do 3 destruct H0.
  destruct H3.
  assert (Ancestor g n1 x0 \/ Exporting g n1 n2).
  - clear H0 H2.
    apply clos_rt_rtn1 in H3.
    induction H3; search.
    apply clos_rtn1_rt in H3.
    apply clos_rt_rt1n in H1.
    invert H1; search.
    apply clos_rt1n_rt in H5.
    unfold Module in H.
    specialize (H y0 z y).
    do 3 feed H.
    feed IHclos_refl_trans_n1.
    destruct IHclos_refl_trans_n1; search.
    right.
    apply rt_trans with (y := y); search.
  - destruct H5; search.
    assert (Ancestor g n1 x \/ Exporting g n1 n2).
    + clear H0.
      destruct H4; search.
      destruct H0.
      * apply clos_rt_rt1n in H5.
        invert H5; search.
        apply clos_rt1n_rt in H6.
        unfold Module in H.
        specialize (H y x0 x).
        do 2 feed H.
      * left.
        apply rt_trans with (y := x0); search.
    + clear H5.
      destruct H6; search.
      clear H2.
      apply clos_rt_rtn1 in H0.
      induction H0; search.
      destruct IHclos_refl_trans_n1; search.
      * apply rt_trans with (y := y); search.
      * apply rt_trans with (y := y); search.
        apply rt_trans with (y := z0); search.
Qed.

Hint Resolve encapsulation : main.

(*
  The nodes which can be depended on by a node sandboxed within a module are
  descendants of the module.
*)

Theorem sandboxing Node (g : AdmissibilityGraph Node) n1 n2 n3 :
  Sandboxed g n1 n2 -> Allowed g n2 n3 -> Ancestor g n1 n3.
Proof.
  clean.
  pose proof (encapsulation Node (transpose g) n1 n2 n3).
  feed H1; [ apply -> transpose_sandboxed; search | idtac ].
  feed H1; [ apply -> duality; search | idtac ].
  apply transpose_ancestor.
  search.
Qed.

Hint Resolve sandboxing : main.

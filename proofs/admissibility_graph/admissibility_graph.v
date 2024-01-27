(**********************************)
(**********************************)
(****                          ****)
(****   Admissibility graphs   ****)
(****                          ****)
(**********************************)
(**********************************)

Require Import Coq.Relations.Operators_Properties.
Require Import Coq.Relations.Relation_Operators.
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

#[export] Hint Resolve transpose_involution : main.

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

#[export] Hint Resolve transpose_trusting : main.

Theorem transpose_exporting Node (g : AdmissibilityGraph Node) :
  Exporting g = Trusting (transpose g).
Proof.
  assert (forall n1 n2, Exporting g n1 n2 = Trusting (transpose g) n1 n2);
    search.
Qed.

#[export] Hint Resolve transpose_trusting : main.

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

#[export] Hint Constructors Allowed : main.

(*
  The dependencies allowed by the transpose of a graph are the flipped versions
  of the dependencies allowed by the original graph.
*)

Theorem duality Node (g : AdmissibilityGraph Node) n1 n2 :
  Allowed g n1 n2 <-> Allowed (transpose g) n2 n1.
Proof.
  split; clean; induction H; esearch.
Qed.

#[export] Hint Resolve duality : main.

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

#[export] Hint Resolve reflection : main.

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
  unfold Trusting, Exporting.
  split; clean.
  - induction H.
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
  - induction (clos_rt_rtn1 Node (Trusts g) x n1 H);
    induction (clos_rt_rtn1 Node (Exports g) x0 n2 H0);
    esearch.
Qed.

#[export] Hint Resolve admission : main.

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

#[export] Hint Resolve transpose_parent_child : main.

(*
  If there is a (possibly empty) chain of lineage from one node to another, we
  say the former is an *ancestor* of the latter.
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

#[export] Hint Resolve transpose_parent_child : main.

(* The ancestor relation is a superset of the trusting relation. *)

Theorem trusting_ancestor Node (g : AdmissibilityGraph Node) n1 n2 :
  Trusting g n1 n2 -> Ancestor g n1 n2.
Proof.
  clean.
  induction H; search.
  apply rt_trans with (y := y); search.
Qed.

#[export] Hint Resolve trusting_ancestor : main.

(* The ancestor relation is a superset of the exporting relation. *)

Theorem exporting_ancestor Node (g : AdmissibilityGraph Node) n1 n2 :
  Exporting g n1 n2 -> Ancestor g n1 n2.
Proof.
  clean.
  induction H; search.
  apply rt_trans with (y := y); search.
Qed.

#[export] Hint Resolve exporting_ancestor : main.

(*
  A node *covers* another node if the former is an ancestor of any parents of
  any nodes that have the latter as an ancestor. This doesn't imply that the
  former node can depend on the latter.
*)

Definition Covers [Node] (g : AdmissibilityGraph Node) n1 n2 :=
  forall n3 n4, Ancestor g n2 n3 -> ParentChild g n4 n3 -> Ancestor g n1 n4.

Theorem transpose_covers Node (g : AdmissibilityGraph Node) n1 n2 :
  Covers g n1 n2 <-> Covers (transpose g) n1 n2.
Proof.
  unfold Covers.
  split; clean.
  - apply -> transpose_ancestor.
    apply transpose_ancestor in H0.
    apply transpose_parent_child in H1.
    esearch.
  - apply transpose_ancestor.
    apply -> transpose_ancestor in H0.
    apply -> transpose_parent_child in H1.
    esearch.
Qed.

#[export] Hint Resolve transpose_covers : main.


(*
  If a node covers another, then an ancestor of the former covers any node
  which has the latter as an ancestor.
*)

Theorem coverage_extension Node (g : AdmissibilityGraph Node) n1 n2 n3 n4 :
  Ancestor g n1 n2 ->
  Ancestor g n3 n4 ->
  Covers g n2 n3 ->
  Covers g n1 n4.
Proof.
  unfold Covers.
  clean.
  specialize (H1 n0 n5).
  feed H1.
  - apply rt_trans with (y := n4); search.
  - feed H1.
    apply rt_trans with (y := n2); search.
Qed.

#[export] Hint Resolve coverage_extension : main.

(* A node is a *module* if it covers all of its children. *)

Definition Module [Node] (g : AdmissibilityGraph Node) n1 :=
  forall n2, ParentChild g n1 n2 -> Covers g n1 n2.

Theorem transpose_module Node (g : AdmissibilityGraph Node) n :
  Module g n <-> Module (transpose g) n.
Proof.
  unfold Module.
  split; clean.
  - apply -> transpose_covers.
    apply transpose_parent_child in H0.
    esearch.
  - apply transpose_covers.
    apply -> transpose_parent_child in H0.
    esearch.
Qed.

#[export] Hint Resolve transpose_module : main.

(*
  The nodes within a module which can be depended on from nodes outside the
  module are exported by the module.
*)

Theorem encapsulation Node (g : AdmissibilityGraph Node) n1 n2 n3 :
  Module g n1 ->
  Ancestor g n1 n2 ->
  Allowed g n3 n2 ->
  Ancestor g n1 n3 \/ Exporting g n1 n2.
Proof.
  clean.
  apply admission in H1.
  do 3 destruct H1.
  destruct H2.
  assert (Ancestor g n1 x0 \/ Exporting g n1 n2).
  - clear H1.
    apply clos_rt_rtn1 in H2.
    induction H2; search.
    apply clos_rtn1_rt in H2.
    apply clos_rt_rt1n in H0.
    invert H0; search.
    apply clos_rt1n_rt in H5.
    unfold Module in H.
    specialize (H y0).
    feed H.
    unfold Covers in H.
    specialize (H z y).
    feed H.
    feed H.
    feed IHclos_refl_trans_n1.
    destruct IHclos_refl_trans_n1; search.
    right.
    apply rt_trans with (y := y); search.
  - destruct H4; search.
    assert (Ancestor g n1 x \/ Exporting g n1 n2).
    + clear H1.
      destruct H3; search.
      destruct H1.
      * apply clos_rt_rt1n in H4.
        invert H4; search.
        apply clos_rt1n_rt in H5.
        unfold Module in H.
        specialize (H y).
        feed H.
        unfold Covers in H.
        specialize (H x0 x).
        left.
        do 2 feed H.
      * left.
        apply rt_trans with (y := x0); search.
    + clear H4.
      destruct H5; search.
      apply clos_rt_rtn1 in H1.
      induction H1; search.
      destruct IHclos_refl_trans_n1; search.
      left.
      apply rt_trans with (y := y); search.
Qed.

#[export] Hint Resolve encapsulation : main.

(*
  The nodes within a module which can depend on nodes outside the module are
  trusted by the module.
*)

Theorem sandboxing Node (g : AdmissibilityGraph Node) n1 n2 n3 :
  Module g n1 ->
  Ancestor g n1 n2 ->
  Allowed g n2 n3 ->
  Ancestor g n1 n3 \/ Trusting g n1 n2.
Proof.
  clean.
  pose proof (encapsulation Node (transpose g) n1 n2 n3).
  feed H2; [ apply -> transpose_module; search | idtac ].
  feed H2; [ apply -> transpose_ancestor; search | idtac ].
  feed H2; [ apply -> duality; search | idtac ].
  destruct H2; search.
  apply <- transpose_ancestor in H2.
  search.
Qed.

#[export] Hint Resolve sandboxing : main.

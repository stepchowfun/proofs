(*************************************************)
(*************************************************)
(****                                         ****)
(****   Conflict-free replicated data types   ****)
(****                                         ****)
(*************************************************)
(*************************************************)

Require Import Main.Tactics.

(*
  An *algebraic semilattice* is a commutative, idempotent monoid. Some texts
  define it as a commutative, idempotent semigroup, but the monoidal version is
  more natural for our purposes.
*)

Record algebraicSemilattice [A] (initial : A) (merge : A -> A -> A) := {
  idempotency a : merge a a = a;
  commutativity a b : merge a b = merge b a;
  associativity a b c : merge a (merge b c) = merge (merge a b) c;
  identity a : merge initial a = a;
}.

#[export] Hint Constructors algebraicSemilattice : main.

(*
  A *partial order* is a homogeneous relation that is reflexive, transitive,
  and antisymmetric.
*)

Record partialOrder [A] (R : A -> A -> Prop) := {
  reflexivity a : R a a;
  transitivity a b c : R a b -> R b c -> R a c;
  antisymmetry a b : R a b -> R b a -> a = b;
}.

#[export] Hint Constructors partialOrder : main.

(*
  A *least upper bound* of two elements is an upper bound of those elements
  that is at least as small as any other upper bound of those elements.
*)

Definition upperBound [A] (R : A -> A -> Prop) a b ub := R a ub /\ R b ub.

Definition leastUpperBound [A] (R : A -> A -> Prop) a b bound :=
  upperBound R a b bound /\ forall ub, upperBound R a b ub -> R bound ub.

(*
  An *join-semilattice* is a partial order in which any finite subset of
  elements has a least upper bound. Some texts only require a least upper bound
  for any finite, nonempty subset of elements, but we'll need it for the empty
  set too.

  The partial order is fully determined by the least upper bound function.
*)

Definition order [A] (merge : A -> A -> A) a b := merge a b = b.

Theorem partialOrderDeterminedByLeastUpperBounds
  (A : Type) (merge : A -> A -> A) (R : A -> A -> Prop)
: partialOrder R ->
  (forall a b, leastUpperBound R a b (merge a b)) ->
  forall a b, R a b <-> order merge a b.
Proof.
  unfold leastUpperBound, upperBound, order.
  clean.
  split; clean.
  - apply antisymmetry with (R := R); search.
    + apply H0; search.
    + apply H0.
  - specialize (H0 a b).
    search.
Qed.

#[export] Hint Resolve partialOrderDeterminedByLeastUpperBounds : main.

Definition joinSemilattice [A] (initial : A) (merge : A -> A -> A) :=
  partialOrder (order merge) /\
  (forall a, order merge initial a) /\
  (forall a b, leastUpperBound (order merge) a b (merge a b)).

(* These two types of semilattices are equivalent. *)

Theorem semilatticeCorrespondence A (initial : A) (merge : A -> A -> A) :
  algebraicSemilattice initial merge <-> joinSemilattice initial merge.
Proof.
  split; clean; destruct H.
  - split.
    + search.
    + unfold order, leastUpperBound, upperBound.
      repeat split; search.
  - unfold leastUpperBound, upperBound in H0.
    split; clean.
    + specialize (H1 a a). search.
    + apply antisymmetry with (R := order merge); search; apply H1;
      specialize (H1 a b) + specialize (H1 b a);
      solve [search].
    + apply antisymmetry with (R := order merge); search;
      repeat (apply H1; split);
      apply transitivity with (b := merge a b) +
        apply transitivity with (b := merge b c);
      search;
      apply (H1 a _) +
        apply (H1 b _) +
        apply (H1 (merge _ _) _) +
        apply (H1 _ (merge _ _)); solve [search].
    + apply antisymmetry with (R := order merge); search; apply H1; search.
Qed.

#[export] Hint Resolve semilatticeCorrespondence : main.

(*
  A state-based CRDT is a semilattice of states (as defined above) with a
  monotonic update operation.
*)

Record stateCRDT
  [A T] (initial : A) (merge : A -> A -> A) (update : T -> A -> A)
:= {
  semilattice : algebraicSemilattice initial merge;
  monotonicity x a : merge a (update x a) = update x a;
}.

#[export] Hint Constructors stateCRDT : main.

(*
  The *history* of a node is the graph of operations that led to the current
  state. Update operations are identified with a natural number ID for use in
  stating the strong convergence theorem.
*)

Inductive history T :=
| opEmpty : history T
| opUpdate : nat -> history T -> T -> history T
| opMerge : history T -> history T -> history T.

#[export] Hint Constructors history : main.

(*
  The argument and prior history for each update operation are determined by
  the update ID.
*)

Inductive historyConsistent
  [T]
  (getHistory : nat -> history T)
  (getArgument : nat -> T)
: history T -> Prop
:=
| emptyConsistent : historyConsistent _ _ (opEmpty T)
| updateConsistent :
  forall n h x,
  getHistory n = h ->
  getArgument n = x ->
  historyConsistent _ _ h -> historyConsistent _ _ (opUpdate _ n h x)
| mergeConsistent :
  forall h1 h2,
  historyConsistent _ _ h1 ->
  historyConsistent _ _ h2 ->
  historyConsistent _ _ (opMerge _ h1 h2).

#[export] Hint Constructors historyConsistent : main.

(*
  The following relation indicates when a node's history contains an update
  with a given ID.
*)

Inductive inHistory [T] (n1 : nat) : history T -> Prop :=
| inThisUpdate:
  forall n2 h x, inHistory n1 h -> inHistory n1 (opUpdate _ n2 h x)
| inNestedUpdate :
  forall h x, inHistory n1 (opUpdate _ n1 h x)
| inMergeLeft :
  forall h1 h2, inHistory n1 h1 -> inHistory n1 (opMerge _ h1 h2)
| inMergeRight :
  forall h1 h2, inHistory n1 h2 -> inHistory n1 (opMerge _ h1 h2).

#[export] Hint Constructors inHistory : main.

(* This function replays a node's history to compute its current state. *)

Fixpoint run
  [A T]
  (initial : A)
  (merge : A -> A -> A)
  (update : T -> A -> A)
  (h1 : history T)
:=
  match h1 with
  | opEmpty _ => initial
  | opUpdate _ n h x => update x (run initial merge update h)
  | opMerge _ h2 h3 =>
    merge (run initial merge update h2) (run initial merge update h3)
  end.

(*
  We'll need the following lemma, which states that the current state of a node
  is at least as "large" (according to the partial order of the CRDT) as any
  prior states resulting from update operations in the history.
*)

Theorem runUpperBound
    A T
    (initial : A)
    (merge : A -> A -> A)
    (update : T -> A -> A)
    (h : history T)
    getHistory
    getArgument
    n
: stateCRDT initial merge update ->
  historyConsistent getHistory getArgument h ->
  inHistory n h ->
  order merge
    (update (getArgument n) (run initial merge update (getHistory n)))
    (run initial merge update h).
Proof.
  clean.
  destruct (semilatticeCorrespondence A initial merge).
  clear H3.
  feed H2.
  destruct H2, H3.
  induction h; search; invert H0.
  - feed IHh.
    invert H1.
    + feed IHh.
      apply transitivity with (
        b := (run initial merge update (getHistory n0))
      ); search.
      clean.
      apply monotonicity with (initial := initial).
      search.
    + clean.
      apply idempotency with (initial := initial).
      search.
  - feed IHh1.
    feed IHh2.
    invert H1;
      [
        feed IHh1;
          apply transitivity with (b := (run initial merge update h1));
          search |
        feed IHh2;
          apply transitivity with (b := (run initial merge update h2));
          search
      ];
      clean;
      specialize (
        H4
          (run initial merge update h1)
          (run initial merge update h2)
      );
      destruct H4;
      destruct H0;
      search.
Qed.

#[export] Hint Resolve runUpperBound : main.

(*
  We're now ready to state and prove the strong convergence theorem: any two
  nodes with the same set of updates in their histories are in the same state.
*)

Theorem strongConvergence
  A T
  (initial : A)
  (merge : A -> A -> A)
  (update : T -> A -> A)
: stateCRDT initial merge update ->
  forall h1 h2,
  (
    exists getHistory getArgument,
    historyConsistent getHistory getArgument h1 /\
    historyConsistent getHistory getArgument h2
  ) ->
  (forall n, inHistory n h1 <-> inHistory n h2) ->
  run initial merge update h1 = run initial merge update h2.
Proof.
  clean.
  destruct H.
  destruct (semilatticeCorrespondence A initial merge).
  clear H3.
  feed H.
  destruct H, H3.
  apply antisymmetry with (R := order merge); search.
  - assert (forall n, inHistory n h1 -> inHistory n h2); try apply H1.
    clear H1.
    induction h1; search.
    + invert H0.
      repeat feed IHh1.
    + invert H0.
      repeat feed IHh1_1.
      repeat feed IHh1_2.
      destruct (
        H4
          (run initial merge update h1_1)
          (run initial merge update h1_2)
      ).
      assert (
        upperBound
          (order merge)
          (run initial merge update h1_1)
          (run initial merge update h1_2)
          (run initial merge update h2)
        ); search.
  - assert (forall n, inHistory n h2 -> inHistory n h1); try apply H1.
    clear H1.
    induction h2; search.
    + invert H2.
      repeat feed IHh2.
    + invert H2.
      repeat feed IHh2_1.
      repeat feed IHh2_2.
      destruct (
        H4
          (run initial merge update h2_1)
          (run initial merge update h2_2)
      ).
      assert (
        upperBound
          (order merge)
          (run initial merge update h2_1)
          (run initial merge update h2_2)
          (run initial merge update h1)
        ); search.
Qed.

#[export] Hint Resolve strongConvergence : main.

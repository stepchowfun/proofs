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
  A *state-based CRDT* is a semilattice of states (as defined above) with a
  query operation and a monotonic update operation.
*)

Record stateCRDT argument result := {
  state : Type;
  initial : state;
  merge : state -> state -> state;
  update : argument -> state -> state;
  query : state -> result;
  semilattice : algebraicSemilattice initial merge;
  monotonicity x a : merge a (update x a) = update x a;
}.

#[export] Hint Constructors stateCRDT : main.

Arguments state [_ _].
Arguments initial [_ _].
Arguments merge [_ _] _ _.
Arguments update [_ _] _ _.
Arguments query [_ _] _.

(*
  The *history* of a node is the graph of operations that led to the current
  state. Update operations are identified with a natural number ID for use in
  stating the strong convergence theorem.
*)

Inductive history [argument result] (crdt : stateCRDT argument result) :=
| opEmpty : history crdt
| opUpdate : nat -> history crdt -> argument -> history crdt
| opMerge : history crdt -> history crdt -> history crdt.

#[export] Hint Constructors history : main.

(*
  The argument and prior history for each update operation are determined by
  the update ID.
*)

Inductive historyConsistent
  [argument result]
  [crdt : stateCRDT argument result]
  (getHistory : nat -> history crdt)
  (getArgument : nat -> argument)
: history crdt -> Prop
:=
| emptyConsistent : historyConsistent _ _ (opEmpty crdt)
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

Inductive inHistory [argument result] [crdt : stateCRDT argument result] n1
: history crdt -> Prop :=
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
  [argument result]
  [crdt : stateCRDT argument result]
  (h1 : history crdt)
:=
  match h1 with
  | opEmpty _ => crdt.(initial)
  | opUpdate _ n h x => crdt.(update) x (run h)
  | opMerge _ h2 h3 => crdt.(merge) (run h2) (run h3)
  end.

(*
  We'll need the following lemma, which states that the current state of a node
  is at least as "large" (according to the partial order of the CRDT) as any
  prior states resulting from update operations in the history.
*)

Theorem runUpperBound
  [argument result]
  (crdt : stateCRDT argument result)
  h
  getHistory
  getArgument
  n
: historyConsistent getHistory getArgument h ->
  inHistory n h ->
  order crdt.(merge)
    (crdt.(update) (getArgument n) (run (getHistory n)))
    (run h).
Proof.
  destruct crdt.
  clean.
  destruct (semilatticeCorrespondence state0 initial0 merge0).
  clear H2.
  feed H1.
  destruct H1, H2.
  induction h; search; invert H.
  - feed IHh.
    invert H0; search.
    feed IHh.
    apply transitivity with (b := run (getHistory n0)); search.
  - feed IHh1.
    feed IHh2.
    invert H0;
      [
        feed IHh1; apply transitivity with (b := run h1); search |
        feed IHh2; apply transitivity with (b := run h2); search
      ];
      clean;
      specialize (H3 (run h1) (run h2));
      destruct H3;
      destruct H;
      search.
Qed.

#[export] Hint Resolve runUpperBound : main.

(*
  We're now ready to state and prove the strong convergence theorem: any two
  nodes with the same set of updates in their histories are in the same state.
*)

Theorem strongConvergence
  [argument result]
  (crdt : stateCRDT argument result)
  (h1 h2 : history crdt)
: (
    exists getHistory getArgument,
    historyConsistent getHistory getArgument h1 /\
    historyConsistent getHistory getArgument h2
  ) ->
  (forall n, inHistory n h1 <-> inHistory n h2) ->
  run h1 = run h2.
Proof.
  clean.
  destruct (
    semilatticeCorrespondence crdt.(state) crdt.(initial) crdt.(merge)
  ).
  clear H3.
  feed H2; [ destruct crdt; search | idtac ].
  destruct H2, H3.
  apply antisymmetry with (R := order crdt.(merge)); search.
  - assert (forall n, inHistory n h1 -> inHistory n h2); try apply H0.
    clear H0.
    induction h1; search; clean; invert H.
    + repeat feed IHh1.
    + repeat feed IHh1_1.
      repeat feed IHh1_2.
      destruct (H4 (run h1_1) (run h1_2)).
      assert (upperBound (order crdt.(merge)) (run h1_1) (run h1_2) (run h2));
        search.
  - assert (forall n, inHistory n h2 -> inHistory n h1); try apply H0.
    clear H0.
    induction h2; search; clean; invert H1.
    + repeat feed IHh2.
    + repeat feed IHh2_1.
      repeat feed IHh2_2.
      destruct (H4 (run h2_1) (run h2_2)).
      assert (upperBound (order crdt.(merge)) (run h2_1) (run h2_2) (run h1));
        search.
Qed.

#[export] Hint Resolve strongConvergence : main.

(* A simple CRDT: a Boolean event flag *)

Program Definition booleanEventFlag : stateCRDT unit bool :=
  {|
    state := bool;
    initial := false;
    merge := orb;
    update _ _ := true;
    query := id;
  |}.
Next Obligation.
  split; clean.
  - destruct a; search.
  - destruct a, b; search.
  - destruct a, b, c; search.
  - search.
Qed.
Next Obligation.
  destruct a; search.
Qed.

Compute
  booleanEventFlag.(query)
    (booleanEventFlag.(update) tt booleanEventFlag.(initial)).

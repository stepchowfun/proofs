(*************************************************************)
(*************************************************************)
(****                                                     ****)
(****   State-based conflict-free replicated data types   ****)
(****                                                     ****)
(*************************************************************)
(*************************************************************)

Require Import Main.Tactics.

(*
  The theory of state-based conflict-free replicated data types is based on the
  idea of *bounded semilattices*. We'll give two definitions of this concept
  and prove they are equivalent.

  First, a bounded *algebraic semilattice* is a commutative, idempotent monoid.
*)

Record algebraicSemilattice [A] (initial : A) (merge : A -> A -> A) := {
  idempotency a : merge a a = a;
  commutativity a b : merge a b = merge b a;
  associativity a b c : merge a (merge b c) = merge (merge a b) c;
  identity a : merge initial a = a;
}.

#[export] Hint Constructors algebraicSemilattice : main.

(*
  There other way to define a semilattice is a bit more complicated than the
  algebraic presentation above. Before we introduce it, we need to develop some
  order theory.

  A *partial order* is a homogeneous relation that is reflexive, transitive,
  and antisymmetric.
*)

Record partialOrder [A] (R : A -> A -> Prop) := {
  reflexivity a : R a a;
  transitivity a b c : R a b -> R b c -> R a c;
  antisymmetry a b : R a b -> R b a -> a = b;
}.

#[export] Hint Constructors partialOrder : main.

(* An *upper bound* of two elements is at least as large as those elements. *)

Definition upperBound [A] (R : A -> A -> Prop) a b ub := R a ub /\ R b ub.

(*
  A *least upper bound* or *join* of two elements is an upper bound of those
  elements that is at least as small as any other upper bound of those
  elements.
*)

Definition leastUpperBound [A] (R : A -> A -> Prop) a b bound :=
  upperBound R a b bound /\ forall ub, upperBound R a b ub -> R bound ub.

(*
  The least upper bounds, if they exist, completely determine the partial
  order.
*)

Definition order [A] (join : A -> A -> A) a b := join a b = b.

Theorem partialOrderDeterminedByLeastUpperBounds
  A a b (join : A -> A -> A) (R : A -> A -> Prop)
: partialOrder R ->
  leastUpperBound R a b (join a b) ->
  R a b <-> order join a b.
Proof.
  unfold leastUpperBound, upperBound, order.
  search.
Qed.

#[export] Hint Resolve partialOrderDeterminedByLeastUpperBounds : main.

(*
  A bounded *join-semilattice* is a partial order in which any finite subset of
  elements has a least upper bound.
*)

Definition joinSemilattice [A] (initial : A) (join : A -> A -> A) :=
  partialOrder (order join) /\
  (forall a, order join initial a) /\
  (forall a b, leastUpperBound (order join) a b (join a b)).

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
  A *state-based CRDT* is a bounded semilattice of states (as defined above)
  with a query operation and a monotonic update operation.
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

Arguments state [_ _].
Arguments initial [_ _].
Arguments merge [_ _] _ _.
Arguments update [_ _] _ _.
Arguments query [_ _] _.

#[export] Hint Constructors stateCRDT : main.

(*
  The *history* of a node is the graph of operations that led to the current
  state. Update operations are identified with a natural number ID for use in
  stating the strong convergence theorem.
*)

Inductive history [argument result] (crdt : stateCRDT argument result) :=
| opEmpty : history _
| opUpdate : nat -> argument -> history _ -> history _
| opMerge : history _ -> history _ -> history _.

Arguments opUpdate [_ _ _] _ _ _.
Arguments opMerge [_ _ _] _ _.

#[export] Hint Constructors history : main.

(*
  The argument and prior history for each update operation should be determined
  by the update ID. To formalize that, we define the following consistency
  predicate.
*)

Inductive historyConsistent
  [argument result]
  [crdt : stateCRDT argument result]
  (getArgument : nat -> option argument)
  (getHistory : nat -> option (history crdt))
: history crdt -> Prop
:=
| emptyConsistent : historyConsistent _ _ (opEmpty crdt)
| updateConsistent :
  forall n h x,
  getArgument n = Some x ->
  getHistory n = Some h ->
  historyConsistent _ _ h ->
  historyConsistent _ _ (opUpdate n x h)
| mergeConsistent :
  forall h1 h2,
  historyConsistent _ _ h1 ->
  historyConsistent _ _ h2 ->
  historyConsistent _ _ (opMerge h1 h2).

#[export] Hint Constructors historyConsistent : main.

(*
  The following relation indicates when a node's history contains an update
  with a given ID.
*)

Inductive inHistory [argument result] [crdt : stateCRDT argument result] n1
: history crdt -> Prop :=
| inThisUpdate:
  forall n2 h x, inHistory _ h -> inHistory _ (opUpdate n2 x h)
| inNestedUpdate :
  forall h x, inHistory _ (opUpdate n1 x h)
| inMergeLeft :
  forall h1 h2, inHistory _ h1 -> inHistory _ (opMerge h1 h2)
| inMergeRight :
  forall h1 h2, inHistory _ h2 -> inHistory _ (opMerge h1 h2).

#[export] Hint Constructors inHistory : main.

(* This function replays a node's history to compute its current state. *)

Fixpoint run
  [argument result]
  [crdt : stateCRDT argument result]
  (h1 : history crdt)
:=
  match h1 with
  | opEmpty _ => crdt.(initial)
  | opUpdate n x h2 => crdt.(update) x (run h2)
  | opMerge h2 h3 => crdt.(merge) (run h2) (run h3)
  end.

(*
  We'll need the following lemma, which states that the current state of a node
  is at least as "large" (according to the partial order of the CRDT) as any
  prior states resulting from update operations in the node's history.
*)

Theorem runUpperBound
  argument result
  (crdt : stateCRDT argument result)
  getArgument getHistory h1 h2 n x
: historyConsistent getArgument getHistory h1 ->
  inHistory n h1 ->
  Some x = getArgument n ->
  Some h2 = getHistory n ->
  order crdt.(merge) (crdt.(update) x (run h2)) (run h1).
Proof.
  destruct crdt.
  clean.
  destruct (semilatticeCorrespondence state0 initial0 merge0).
  clear H4.
  feed H3.
  destruct H3, H4.
  induction h1; search; invert H; invert H0; clean.
  - apply transitivity with (b := run h1); search.
  - replace x with a; search.
    replace h2 with h1; search.
  - apply transitivity with (b := run h1_1); search.
    specialize (H5 (run h1_1) (run h1_2)).
    destruct H5, H.
    search.
  - apply transitivity with (b := run h1_2); search.
    specialize (H5 (run h1_1) (run h1_2)).
    destruct H5, H.
    search.
Qed.

#[export] Hint Resolve runUpperBound : main.

(*
  We're now ready to state and prove the strong convergence theorem: any two
  nodes with the same set of updates in their histories are in the same state.
*)

Theorem strongConvergence
  argument result
  (crdt : stateCRDT argument result)
  (h1 h2 : history crdt)
: (
    exists getArgument getHistory,
    historyConsistent getArgument getHistory h1 /\
    historyConsistent getArgument getHistory h2
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
      eSearch.
    + repeat feed IHh1_1.
      repeat feed IHh1_2.
      destruct (H4 (run h1_1) (run h1_2)).
      assert (upperBound (order crdt.(merge)) (run h1_1) (run h1_2) (run h2));
        search.
  - assert (forall n, inHistory n h2 -> inHistory n h1); try apply H0.
    clear H0.
    induction h2; search; clean; invert H1.
    + repeat feed IHh2.
      eSearch.
    + repeat feed IHh2_1.
      repeat feed IHh2_2.
      destruct (H4 (run h2_1) (run h2_2)).
      assert (upperBound (order crdt.(merge)) (run h2_1) (run h2_2) (run h1));
        search.
Qed.

#[export] Hint Resolve strongConvergence : main.

(* A simple state-based CRDT: a Boolean event flag *)

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

Definition exampleHistory : history booleanEventFlag :=
  opMerge
    (opEmpty _)
    (
      opUpdate 1 tt
        (opUpdate 0 tt (opEmpty _))
    ).

Goal
  exists getArgument getHistory,
  historyConsistent getArgument getHistory exampleHistory.
Proof.
  exists (
    fun a =>
      match a with
      | 0 => Some tt
      | 1 => Some tt
      | _ => None
      end
  ).
  exists (
    fun a =>
      match a with
      | 0 => Some (opEmpty _)
      | 1 => Some (opUpdate 0 tt (opEmpty _))
      | _ => None
      end
  ).
  search.
Qed.

Compute run exampleHistory.

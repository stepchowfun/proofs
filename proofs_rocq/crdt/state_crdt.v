(*************************************************************)
(*************************************************************)
(****                                                     ****)
(****   State-based conflict-free replicated data types   ****)
(****                                                     ****)
(*************************************************************)
(*************************************************************)

Require Import main.tactics.

(*
  The theory of state-based conflict-free replicated data types is based on the
  idea of *bounded semilattices*. We'll give two definitions of this concept
  and prove they are equivalent.

  First, a bounded *algebraic semilattice* is an idempotent commutative monoid.
*)

Record AlgebraicSemilattice [T] (initial : T) (merge : T -> T -> T) := {
  idempotency x : merge x x = x;
  commutativity x y : merge x y = merge y x;
  associativity x y z : merge x (merge y z) = merge (merge x y) z;
  identity x : merge initial x = x;
}.

Hint Constructors AlgebraicSemilattice : main.

(*
  There other way to define a semilattice is a bit more complicated than the
  algebraic presentation above. Before we introduce it, we need to develop some
  order theory.

  A *partial order* is a homogeneous relation that is reflexive, transitive,
  and antisymmetric.
*)

Record PartialOrder [T] (R : T -> T -> Prop) := {
  reflexivity x : R x x;
  transitivity x y z : R x y -> R y z -> R x z;
  antisymmetry x y : R x y -> R y x -> x = y;
}.

Hint Constructors PartialOrder : main.

(* An *upper bound* of two elements is at least as large as those elements. *)

Definition UpperBound [T] (R : T -> T -> Prop) x y ub := R x ub /\ R y ub.

(*
  A *least upper bound* or *join* of two elements is an upper bound of those
  elements that is at least as small as any other upper bound of those
  elements.
*)

Definition LeastUpperBound [T] (R : T -> T -> Prop) x y bound :=
  UpperBound R x y bound /\ forall ub, UpperBound R x y ub -> R bound ub.

(*
  The least upper bounds, if they exist, completely determine the partial
  order.
*)

Definition Order [T] (join : T -> T -> T) x y := join x y = y.

Theorem partial_order_determined_by_least_upper_bounds
  T x y (join : T -> T -> T) (R : T -> T -> Prop)
: PartialOrder R ->
  LeastUpperBound R x y (join x y) ->
  R x y <-> Order join x y.
Proof.
  unfold LeastUpperBound, UpperBound, Order.
  search.
Qed.

Hint Resolve partial_order_determined_by_least_upper_bounds : main.

(*
  A bounded *join-semilattice* is a partial order in which any finite subset of
  elements has a least upper bound.
*)

Definition JoinSemilattice [T] (initial : T) (join : T -> T -> T) :=
  PartialOrder (Order join) /\
  (forall x, Order join initial x) /\
  forall x y, LeastUpperBound (Order join) x y (join x y).

(* These two types of semilattices are equivalent. *)

Theorem semilattice_correspondence T (initial : T) (merge : T -> T -> T) :
  AlgebraicSemilattice initial merge <-> JoinSemilattice initial merge.
Proof.
  split; clean; destruct H.
  - split.
    + search.
    + unfold Order, LeastUpperBound, UpperBound.
      repeat split; search.
  - unfold LeastUpperBound, UpperBound in H0.
    split; clean; search.
    + specialize (H1 x x).
      search.
    + apply antisymmetry with (R := Order merge); search; apply H1;
      specialize (H1 x y) + specialize (H1 y x);
      solve [search].
    + apply antisymmetry with (R := Order merge); search;
      repeat (apply H1; split).
      * apply transitivity with (y := merge x y); search.
        -- specialize (H1 x y). search.
        -- specialize (H1 (merge x y) z). search.
      * apply transitivity with (y := merge x y); search.
        -- specialize (H1 x y). search.
        -- specialize (H1 (merge x y) z). search.
      * apply transitivity with (y := merge y z); search.
        -- specialize (H1 y z). search.
        -- specialize (H1 x (merge y z)). search.
      * apply transitivity with (y := merge y z); search.
        -- specialize (H1 y z). search.
        -- specialize (H1 x (merge y z)). search.
Qed.

Hint Resolve semilattice_correspondence : main.

(*
  A *state-based CRDT* is a bounded semilattice of states (as defined above)
  with a query operation and a monotonic update operation.
*)

Record Crdt A Q := {
  State : Type;
  initial : State;
  merge : State -> State -> State;
  update : A -> State -> State;
  query : State -> Q;
  semilattice : AlgebraicSemilattice initial merge;
  monotonicity x a : merge a (update x a) = update x a;
}.

Arguments State [_ _].
Arguments initial [_ _].
Arguments merge [_ _] _ _.
Arguments update [_ _] _ _.
Arguments query [_ _] _.

Hint Constructors Crdt : main.

(*
  The *history* of a node is the graph of operations that led to the current
  state. Update operations are identified with a natural number ID for use in
  stating the strong convergence theorem.
*)

Inductive History [A Q] (crdt : Crdt A Q) :=
| op_empty : History _
| up_update : nat -> A -> History _ -> History _
| op_merge : History _ -> History _ -> History _.

Arguments up_update [_ _ _] _ _ _.
Arguments op_merge [_ _ _] _ _.

Hint Constructors History : main.

(*
  Any updates with the same ID should be identical. To formalize that, we
  define the following consistency predicate.
*)

Inductive HistoryConsistent
  [A Q] [crdt : Crdt A Q]
  (get_update : nat -> option (History crdt))
: History crdt -> Prop :=
| empty_consistent : HistoryConsistent _ (op_empty crdt)
| update_consistent :
  forall n h x,
  get_update n = Some (up_update n x h) ->
  HistoryConsistent _ h ->
  HistoryConsistent _ (up_update n x h)
| merge_consistent :
  forall h1 h2,
  HistoryConsistent _ h1 ->
  HistoryConsistent _ h2 ->
  HistoryConsistent _ (op_merge h1 h2).

Hint Constructors HistoryConsistent : main.

(*
  The following relation indicates when a node's history contains an update
  with a given ID.
*)

Inductive InHistory [A Q] [crdt : Crdt A Q] n1
: History crdt -> Prop :=
| in_this_update:
  forall n2 h x, InHistory _ h -> InHistory _ (up_update n2 x h)
| in_nested_update :
  forall h x, InHistory _ (up_update n1 x h)
| in_merge_left :
  forall h1 h2, InHistory _ h1 -> InHistory _ (op_merge h1 h2)
| in_merge_right :
  forall h1 h2, InHistory _ h2 -> InHistory _ (op_merge h1 h2).

Hint Constructors InHistory : main.

(* This function replays a node's history to compute its current state. *)

Fixpoint run [A Q] [crdt : Crdt A Q] (h1 : History crdt) :=
  match h1 with
  | op_empty _ => crdt.(initial)
  | up_update n x h2 => crdt.(update) x (run h2)
  | op_merge h2 h3 => crdt.(merge) (run h2) (run h3)
  end.

(*
  We'll need the following lemma, which states that the current state of a node
  is at least as "large" (according to the partial order of the CRDT) as any
  prior states resulting from update operations in the node's history.
*)

Theorem run_upper_bound
  A Q
  (crdt : Crdt A Q)
  get_update h1 h2 n x
: HistoryConsistent get_update h1 ->
  InHistory n h1 ->
  let update := up_update n x h2 in
  get_update n = Some update ->
  Order crdt.(merge) (run update) (run h1).
Proof.
  destruct crdt.
  clean.
  subst update1.
  destruct (semilattice_correspondence State0 initial0 merge0).
  clear H3.
  feed H2.
  destruct H2, H3.
  induction h1; search; invert H; invert H0; clean.
  - apply transitivity with (y := run h1); search.
  - rewrite H1 in H7.
    replace x with a; search.
    replace h2 with h1; search.
  - apply transitivity with (y := run h1_1); search.
    specialize (H4 (run h1_1) (run h1_2)).
    destruct H4, H.
    search.
  - apply transitivity with (y := run h1_2); search.
    specialize (H4 (run h1_1) (run h1_2)).
    destruct H4, H.
    search.
Qed.

Hint Resolve run_upper_bound : main.

(*
  We're now ready to state and prove the strong convergence theorem: any two
  nodes with the same set of updates in their histories are in the same state.
*)

Theorem strong_convergence
  A Q
  (crdt : Crdt A Q)
  (h1 h2 : History crdt)
  get_update
: HistoryConsistent get_update h1 ->
  HistoryConsistent get_update h2 ->
  (forall n, InHistory n h1 <-> InHistory n h2) ->
  run h1 = run h2.
Proof.
  clean.
  destruct (
    semilattice_correspondence crdt.(State) crdt.(initial) crdt.(merge)
  ).
  clear H3.
  feed H2; [ destruct crdt; search | idtac ].
  destruct H2, H3.
  apply antisymmetry with (R := Order crdt.(merge)); search.
  - assert (forall n, InHistory n h1 -> InHistory n h2); try apply H1.
    clear H1.
    induction h1; search; clean; invert H.
    + repeat feed IHh1.
      esearch.
    + repeat feed IHh1_1.
      repeat feed IHh1_2.
      destruct (H4 (run h1_1) (run h1_2)).
      assert (UpperBound (Order crdt.(merge)) (run h1_1) (run h1_2) (run h2));
        search.
  - assert (forall n, InHistory n h2 -> InHistory n h1); try apply H1.
    clear H1.
    induction h2; search; clean; invert H0.
    + repeat feed IHh2.
      esearch.
    + repeat feed IHh2_1.
      repeat feed IHh2_2.
      destruct (H4 (run h2_1) (run h2_2)).
      assert (UpperBound (Order crdt.(merge)) (run h2_1) (run h2_2) (run h1));
        search.
Qed.

Hint Resolve strong_convergence : main.

(* A simple state-based CRDT: a Boolean event flag *)

#[program] Definition boolean_event_flag : Crdt unit bool :=
  {|
    State := bool;
    initial := false;
    merge := orb;
    update _ _ := true;
    query := id;
  |}.
Next Obligation.
  split; clean.
  - destruct x; search.
  - destruct x, y; search.
  - destruct x, y, z; search.
  - search.
Qed.

Definition example_history : History boolean_event_flag :=
  op_merge (op_empty _) (up_update 1 tt (up_update 0 tt (op_empty _))).

Goal exists get_update, HistoryConsistent get_update example_history.
Proof.
  exists (
    fun a =>
      match a with
      | 0 => Some (up_update 0 tt (op_empty _))
      | 1 => Some (up_update 1 tt (up_update 0 tt (op_empty _)))
      | _ => None
      end
  ).
  search.
Qed.

Compute run example_history.

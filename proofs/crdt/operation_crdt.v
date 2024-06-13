(*****************************************************************)
(*****************************************************************)
(****                                                         ****)
(****   Operation-based conflict-free replicated data types   ****)
(****                                                         ****)
(*****************************************************************)
(*****************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinIntDef.
Require Import main.crdt.state_crdt(PartialOrder(..)).
Require Import main.tactics.

Import Coq.Lists.List.ListNotations.
Import Coq.ZArith.BinIntDef.Z.

(*
  The data for an operation-based conflict-free replicated data type consists
  of set of states with an initial state, a query method, an update method, and
  a delivery precondition. The update method returns an operation which can be
  interpreted as a state transformer to be broadcasted to other nodes. Later,
  we'll introduce the laws that these data must satisfy to prove the strong
  convergence theorem.
*)

Record CrdtData A Q := {
  State : Type;
  Operation : Type;
  initial : State;
  update : A -> State -> Operation;
  interpret : Operation -> State -> State;
  query : State -> Q;
  Precondition : State -> Operation -> Prop;
}.

Arguments State [_ _].
Arguments Operation [_ _].
Arguments initial [_ _].
Arguments update [_ _] _ _.
Arguments interpret [_ _] _ _.
Arguments query [_ _] _.
Arguments Precondition [_ _] _ _.

Hint Constructors CrdtData : main.

(*
  The history of a node is a list of operations. `o :: h` is understood as a
  history with `o` as the final operation (even though this position is
  traditionally considered the beginning of the list). The following function
  replays a node's history to compute its current state.
*)

Fixpoint run [A Q] (CrdtData : CrdtData A Q) (h1 : list CrdtData.(Operation))
:=
  match h1 with
  | [] => CrdtData.(initial)
  | o :: h2 => CrdtData.(interpret) o (run CrdtData h2)
  end.

(*
  A history is *valid* when the precondition is satisfied before each
  operation.
*)

Inductive HistoryValid [A Q] (crdt_data : CrdtData A Q)
: list crdt_data.(Operation) -> Prop :=
| empty_valid : HistoryValid _ []
| operation_valid o h :
  HistoryValid _ h ->
  crdt_data.(Precondition) (run crdt_data h) o ->
  HistoryValid _ (o :: h).

Hint Constructors HistoryValid : main.

(*
  A history is *consistent* with a partial order when every operation in the
  history is not less than or equal to the previous operations in the history.
*)

Inductive HistoryConsistent [T] (R : T -> T -> Prop) : list T -> Prop :=
| empty_consistent : HistoryConsistent _ []
| operation_consistent o1 h :
  HistoryConsistent _ h ->
  (forall o2, In o2 h -> ~ R o1 o2) ->
  HistoryConsistent _ (o1 :: h).

Hint Constructors HistoryConsistent : main.

(*
  A partial order is *satisfactory* for a set of operations if every history
  that is consistent with that order and consists only of operations in that
  set is valid.
*)

Definition OrderSatisfactory
  [A Q]
  (crdt_data : CrdtData A Q)
  (P : crdt_data.(Operation) -> Prop)
  (R : crdt_data.(Operation) -> crdt_data.(Operation) -> Prop)
:=
  PartialOrder R /\
  forall h,
    (forall o, In o h -> P o) ->
    HistoryConsistent R h ->
    HistoryValid crdt_data h.

(*
  If two histories that differ only in the order of their last two operations
  are both consistent with a partial order that is satisfactory for the
  operations in those histories, we say those last two operations are
  *concurrent*. They *commute* if both histories result in the same final
  state. In the context of *operation-based CRDTs*, concurrent operations are
  required to commute.
*)

Record Crdt [A Q] (crdt_data : CrdtData A Q) := {
  commutativity R h o1 o2 :
    OrderSatisfactory crdt_data (fun o3 => In o3 h \/ o3 = o1 \/ o3 = o2) R ->
    HistoryConsistent R (o1 :: o2 :: h) ->
    HistoryConsistent R (o2 :: o1 :: h) ->
    let s := run crdt_data h in
    crdt_data.(interpret) o1 (crdt_data.(interpret) o2 s) =
      crdt_data.(interpret) o2 (crdt_data.(interpret) o1 s);
}.

Hint Constructors Crdt : main.

(*
  We're now ready to state and prove the strong convergence theorem: any two
  nodes with the same set of operations in their histories end up in the same
  state if their histories are consistent with an order that is satisfactory
  for the operations in those histories.
*)

Theorem strong_convergence
  A Q
  (crdt_data : CrdtData A Q)
  (crdt : Crdt crdt_data)
  (h1 h2 : list crdt_data.(Operation))
  R
: OrderSatisfactory crdt_data (fun o => In o h2) R ->
  HistoryConsistent R h1 ->
  HistoryConsistent R h2 ->
  (forall o, In o h1 <-> In o h2) ->
  run crdt_data h1 = run crdt_data h2.
Proof.
  unfold OrderSatisfactory.
  clean.
  outro h2.
  induction h1; clean.
  - destruct h2; search.
    specialize (H2 o); search.
  - assert (
      In a h2 ->
      exists h3,
      (forall o, In o h2 <-> In o (a :: h3)) /\
      run crdt_data h2 = run crdt_data (a :: h3) /\
      HistoryConsistent R (a :: h3)
    ).
    + assert (forall o, In o h2 -> R a o -> a = o).
      * clean.
        invert H0.
        specialize (H2 o).
        specialize (H9 o).
        search.
      * clear h1 H0 H2 IHh1.
        outro h2.
        induction h2; search.
        clean.
        destruct H0.
        -- exists h2.
           search.
        -- invert H1.
           do 3 feed IHh2.
           destruct IHh2.
           destruct H1.
           destruct H2.
           exists (a0 :: x).
           repeat split; clean.
           ++ destruct H8; search.
              specialize (H1 o); search.
           ++ repeat destruct H8; search.
              specialize (H1 o); search.
           ++ rewrite H2.
              pose proof (crdt.(commutativity crdt_data) R x a0 a).
              cbn in H8.
              feed H8.
              ** unfold OrderSatisfactory.
                 split; search.
                 clean.
                 apply H3; search.
                 clean.
                 specialize (H9 o H11).
                 destruct H9; search.
                 specialize (H1 o).
                 search.
              ** feed H8.
                 --- constructor.
                     +++ constructor; invert H5; search.
                     +++ clean.
                         apply H7.
                         specialize (H1 o2).
                         search.
                 --- feed H8.
                     constructor.
                     +++ constructor.
                         *** invert H5.
                             search.
                         *** clean.
                             apply H7.
                             specialize (H1 o2).
                             search.
                     +++ clean.
                         destruct H9.
                         *** specialize (H4 a0).
                             specialize (H7 a).
                             search.
                         *** invert H5.
                             search.
           ++ apply operation_consistent; clean.
              ** apply operation_consistent; clean.
                 --- invert H5.
                     search.
                 --- apply H7.
                     specialize (H1 o2).
                     search.
              ** destruct H8.
                 --- subst o2.
                     specialize (H4 a0).
                     feed H4.
                     intro.
                     feed H4.
                     subst a0.
                     specialize (H7 a).
                     feed H7.
                 --- invert H5.
                     search.
    + feed H4.
      * specialize (H2 a).
        search.
      * do 2 destruct H4.
        destruct H5.
        rewrite H5.
        clean.
        rewrite IHh1 with (h2 := x); search.
        -- invert H0.
           search.
        -- invert H6.
           clean.
           apply H3; search.
           clean.
           specialize (H6 o H8).
           specialize (H4 o).
           search.
        -- invert H6.
           search.
        -- clean.
           destruct (H2 o).
           destruct (H4 o).
           split; clean.
           ++ assert (~ In a h1).
              ** invert H0.
                 destruct H.
                 specialize (H15 a).
                 search.
              ** destruct H9; search.
           ++ assert (~ In a x).
              ** invert H6.
                 destruct H.
                 specialize (H15 a).
                 search.
              ** destruct H8; search.
Qed.

Hint Resolve strong_convergence : main.

(* A simple operation-based CRDT: a counter *)

Open Scope Z_scope.

Definition counter_data : CrdtData bool Z :=
  {|
    State := Z;
    Operation := bool;
    initial := 0;
    update x _ := x;
    interpret o s := if o then s + 1 else s - 1;
    query s := s;
    Precondition _ _ := True;
  |}.

Program Definition counter : Crdt counter_data := {| commutativity := _ |}.

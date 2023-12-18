(*****************************************************************)
(*****************************************************************)
(****                                                         ****)
(****   Operation-based conflict-free replicated data types   ****)
(****                                                         ****)
(*****************************************************************)
(*****************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.ZArith.BinIntDef.
Require Import Main.CRDT.StateCRDT(partialOrder(..)).
Require Import Main.Tactics.

Import Coq.Lists.List.ListNotations.
Import Coq.ZArith.BinIntDef.Z.

(*
  The data for an operation-based conflict-free replicated data type consists
  of set of states with an initial state, a query method, an update method, and
  a delivery precondition. The update method returns an operation which can be
  interpreted as a state transformer.
*)

Record crdtData argument result := {
  state : Type;
  operation : Type;
  initial : state;
  update : argument -> state -> operation;
  interpret : operation -> state -> state;
  query : state -> result;
  precondition : state -> operation -> Prop;
}.

Arguments state [_ _].
Arguments operation [_ _].
Arguments initial [_ _].
Arguments update [_ _] _ _.
Arguments interpret [_ _] _ _.
Arguments query [_ _] _.
Arguments precondition [_ _] _ _.

#[export] Hint Constructors crdtData : main.

(*
  The history of a node is a list of operations. Here, `o :: h` signifies a
  history with `o` as the final operation (even though this position is
  traditionally considered the beginning of the list). The following function
  replays a node's history to compute its current state.
*)

Fixpoint run
  [argument result]
  (crdtData : crdtData argument result)
  (h1 : list crdtData.(operation))
:=
  match h1 with
  | [] => crdtData.(initial)
  | o :: h2 => crdtData.(interpret) o (run crdtData h2)
  end.

(*
  A history is *valid* when the precondition is satisfied before each
  operation.
*)

Inductive historyValid
  [argument result]
  (crdtData : crdtData argument result)
: list crdtData.(operation) -> Prop :=
| emptyValid : historyValid _ []
| operationValid o h :
  historyValid _ h ->
  crdtData.(precondition) (run crdtData h) o ->
  historyValid _ (o :: h).

#[export] Hint Constructors historyValid : main.

(*
  A history is *consistent* with a partial order when every operation in the
  history is not less than or equal to the previous operations in the history.
*)

Inductive historyConsistent [A] (R : A -> A -> Prop) : list A -> Prop :=
| emptyConsistent : historyConsistent _ []
| operationConsistent o1 h :
  historyConsistent _ h ->
  (forall o2, In o2 h -> ~ R o1 o2) ->
  historyConsistent _ (o1 :: h).

#[export] Hint Constructors historyConsistent : main.

(*
  A partial order is *valid* if every history consistent with that order is
  valid.
*)

Definition orderValid
  [argument result]
  (crdtData : crdtData argument result)
  (R : crdtData.(operation) -> crdtData.(operation) -> Prop)
:=
  partialOrder R /\ forall h, historyConsistent R h -> historyValid crdtData h.

(*
  If two histories which are consistent with the same valid partial order
  differ only in the order of their last two operations, we say those two
  operations are *concurrent*. They *commute* if applying them in either order
  results in the same final state. Concurrent operations of an *operation-based
  CRDT* are required to commute.
*)

Record crdt [argument result] (crdtData : crdtData argument result) := {
  commutativity R h o1 o2 :
    orderValid crdtData R ->
    historyConsistent R (o1 :: o2 :: h) ->
    historyConsistent R (o2 :: o1 :: h) ->
    let s := run crdtData h in
    crdtData.(interpret) o1 (crdtData.(interpret) o2 s) =
      crdtData.(interpret) o2 (crdtData.(interpret) o1 s);
}.

#[export] Hint Constructors crdt : main.

(*
  We're now ready to state and prove the strong convergence theorem: any two
  nodes with the same set of updates in their histories are in the same state
  if their histories are consistent with a valid order.
*)

Theorem strongConvergence
  argument result
  (crdtData : crdtData argument result)
  (crdt : crdt crdtData)
  (h1 h2 : list crdtData.(operation))
  R
: orderValid crdtData R ->
  historyConsistent R h1 ->
  historyConsistent R h2 ->
  (forall o, In o h1 <-> In o h2) ->
  run crdtData h1 = run crdtData h2.
Proof.
  unfold orderValid.
  clean.
  outro h2.
  induction h1; clean.
  - destruct h2; search.
    specialize (H2 o); search.
  - assert (
      In a h2 ->
      exists h3,
      (forall o, In o h2 <-> In o (a :: h3)) /\
      run crdtData h2 = run crdtData (a :: h3) /\
      historyConsistent R (a :: h3)
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
              pose proof (crdt.(commutativity crdtData) R x a0 a).
              cbn in H8.
              do 2 feed H8.
              ** constructor.
                 --- constructor; invert H5; search.
                 --- clean.
                     apply H7.
                     specialize (H1 o2).
                     search.
              ** feed H8.
                 constructor.
                 --- constructor.
                     +++ invert H5.
                         search.
                     +++ clean.
                         apply H7.
                         specialize (H1 o2).
                         search.
                 --- clean.
                     destruct H9.
                     +++ specialize (H4 a0).
                         specialize (H7 a).
                         search.
                     +++ invert H5.
                         search.
           ++ apply operationConsistent; clean.
              ** apply operationConsistent; clean.
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

#[export] Hint Resolve strongConvergence : main.

(* A simple operation-based CRDT: a counter *)

Open Scope Z_scope.

Definition counterData : crdtData bool Z :=
  {|
    state := Z;
    operation := bool;
    initial := 0;
    update x _ := x;
    interpret o s := if o then s + 1 else s - 1;
    query s := s;
    precondition _ _ := True;
  |}.

Program Definition counter : crdt counterData := {| commutativity := _ |}.
Next Obligation.
  search.
Qed.

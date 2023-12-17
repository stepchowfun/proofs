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
  To construct *operation-based CRDT*, we need a set of states with an initial
  state, a query method, an update method, and a delivery precondition. The
  update method returns an operation which can be interpreted as a state
  transformer.
*)

Record operationCRDTData argument result := {
  oState : Type;
  oOperation : Type;
  oInitial : oState;
  oUpdate : argument -> oState -> oOperation;
  oInterpret : oOperation -> oState -> oState;
  oQuery : oState -> result;
  oPrecondition : oState -> oOperation -> Prop;
}.

Arguments oState [_ _].
Arguments oOperation [_ _].
Arguments oInitial [_ _].
Arguments oUpdate [_ _] _ _.
Arguments oInterpret [_ _] _ _.
Arguments oQuery [_ _] _.
Arguments oPrecondition [_ _] _ _.

#[export] Hint Constructors operationCRDTData : main.

(*
  The history of a node is a list of operations. Here, `o :: h` signifies a
  history with `o` as the final operation (even though this position is
  traditionally considered the beginning of the list). The following function
  replays a node's history to compute its current state.
*)

Fixpoint run
  [argument result]
  (crdtData : operationCRDTData argument result)
  (h1 : list crdtData.(oOperation))
:=
  match h1 with
  | [] => crdtData.(oInitial)
  | o :: h2 => crdtData.(oInterpret) o (run crdtData h2)
  end.

(*
  A history is *valid* when the precondition is satisfied before each
  operation.
*)

Inductive historyValid
  [argument result]
  (crdtData : operationCRDTData argument result)
: list crdtData.(oOperation) -> Prop
:=
| emptyValid : historyValid _ []
| operationValid o h :
  historyValid _ h ->
  crdtData.(oPrecondition) (run crdtData h) o ->
  historyValid _ (o :: h).

#[export] Hint Constructors historyValid : main.

(*
  A history is *consistent* with a partial order when every operation is not
  less than or equal to the previous operations in the history.
*)

Inductive historyConsistent [A] (R : A -> A -> Prop) : list A -> Prop
:=
| emptyConsistent : historyConsistent _ []
| operationConsistent o1 h :
  historyConsistent _ h ->
  (forall o2, In o2 h -> ~ R o1 o2) ->
  historyConsistent _ (o1 :: h).

#[export] Hint Constructors historyConsistent : main.

(* To qualify as a CRDT, concurrent operations must commute. *)

Record operationCRDT
  [argument result]
  (crdtData : operationCRDTData argument result)
:= {
  oCommutativity R s o1 o2 :
    partialOrder R ->
    (forall h, historyConsistent R h -> historyValid crdtData h) ->
    ((~ R o1 o2) /\ (~ R o2 o1)) ->
    crdtData.(oPrecondition) s o1 ->
    crdtData.(oPrecondition) s o2 ->
    crdtData.(oPrecondition) (crdtData.(oInterpret) o2 s) o1 /\
    crdtData.(oPrecondition) (crdtData.(oInterpret) o1 s) o2 /\
    crdtData.(oInterpret) o1 (crdtData.(oInterpret) o2 s) =
      crdtData.(oInterpret) o2 (crdtData.(oInterpret) o1 s);
}.

#[export] Hint Constructors operationCRDT : main.

(*
  We're now ready to state and prove the strong convergence theorem: any two
  nodes with the same set of updates in their histories are in the same state.
*)

Theorem operationStrongConvergence
  argument result
  (crdtData : operationCRDTData argument result)
  (crdt : operationCRDT crdtData)
  (h1 h2 : list crdtData.(oOperation))
  R
: partialOrder R ->
  (forall h, historyConsistent R h -> historyValid crdtData h) ->
  historyConsistent R h1 ->
  historyConsistent R h2 ->
  (forall o, In o h1 <-> In o h2) ->
  run crdtData h1 = run crdtData h2.
Proof.
  clean.
  outro h2.
  induction h1; clean.
  - destruct h2; search.
    specialize (H3 o); search.
  - assert (
      In a h2 ->
      exists h3,
      (forall o, In o h2 <-> In o (a :: h3)) /\
      run crdtData h2 = run crdtData (a :: h3) /\
      historyConsistent R (a :: h3)
    ).
    + assert (forall o, In o h2 -> R a o -> a = o).
      * clean.
        invert H1.
        specialize (H3 o).
        specialize (H9 o).
        search.
      * clear h1 H1 H3 IHh1.
        outro h2.
        induction h2; search.
        clean.
        destruct H1.
        -- exists h2.
           search.
        -- invert H2.
           do 3 feed IHh2.
           destruct IHh2.
           destruct H2.
           destruct H3.
           exists (a0 :: x).
           repeat split; clean.
           ++ destruct H8; search.
              specialize (H2 o); search.
           ++ repeat destruct H8; search.
              specialize (H2 o); search.
           ++ rewrite H3.
              pose proof (
                crdt.(oCommutativity crdtData) R (run crdtData x) a0 a H H0
              ).
              feed H8.
              ** split; search.
                 specialize (H4 a0).
                 feed H4.
                 intro.
                 feed H4.
                 subst a0.
                 specialize (H7 a).
                 feed H7.
              ** feed H8.
                 --- assert (historyValid crdtData (a0 :: x)).
                     +++ apply H0.
                         constructor.
                         *** invert H5.
                             search.
                         *** clean.
                             apply H7.
                             specialize (H2 o2).
                             search.
                     +++ invert H9.
                         search.
                 --- feed H8.
                     assert (historyValid crdtData (a :: x)); search.
                     invert H9.
                     search.
           ++ apply operationConsistent; clean.
              ** apply operationConsistent; clean.
                 --- invert H5.
                     search.
                 --- apply H7.
                     specialize (H2 o2).
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
      * specialize (H3 a).
        search.
      * do 2 destruct H4.
        destruct H5.
        rewrite H5.
        clean.
        rewrite IHh1 with (h2 := x); search.
        -- invert H1.
           search.
        -- invert H6.
           search.
        -- clean.
           destruct (H3 o).
           destruct (H4 o).
           split; clean.
           ++ assert (~ In a h1).
              ** invert H1.
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

#[export] Hint Resolve operationStrongConvergence : main.

(* A simple operation-based CRDT: a counter *)

Definition counterData : operationCRDTData bool Z :=
  {|
    oState := Z;
    oOperation := bool;
    oInitial := 0%Z;
    oUpdate x _ := x;
    oInterpret o s := (if o then s + 1 else s - 1)%Z;
    oQuery s := s;
    oPrecondition _ _ := True;
  |}.

Program Definition counter : operationCRDT counterData :=
  {|
    oCommutativity := _;
  |}.
Next Obligation.
  search.
Qed.

(**************************************************************************)
(**************************************************************************)
(****                                                                  ****)
(****   Equivalence of state-based and operation-based conflict-free   ****)
(****   replicated data types                                          ****)
(****                                                                  ****)
(**************************************************************************)
(**************************************************************************)

Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import main.tactics.

Require main.crdt.operation_crdt.

Import Coq.Lists.List.ListNotations.

(* We can emulate a state-based CRDT with an operation-based CRDT. *)

Definition operation_crdt_data_from_state_crdt
  [A Q]
  (crdt : state_crdt.Crdt A Q)
: operation_crdt.CrdtData A Q
:=
  {|
    operation_crdt.State := crdt.(state_crdt.State);
    operation_crdt.Operation := crdt.(state_crdt.State);
    operation_crdt.initial := crdt.(state_crdt.initial);
    operation_crdt.update x s := crdt.(state_crdt.update) x s;
    operation_crdt.interpret o s := crdt.(state_crdt.merge) o s;
    operation_crdt.query s := crdt.(state_crdt.query) s;
    operation_crdt.Precondition _ _ := True;
  |}.

Program Definition operation_crdt_from_state_crdt
  [A Q]
  (crdt : state_crdt.Crdt A Q)
: operation_crdt.Crdt (operation_crdt_data_from_state_crdt crdt)
:= {| operation_crdt.commutativity := _ |}.
Next Obligation.
  clean.
  pose proof (crdt.(state_crdt.semilattice _ _)).
  rewrite state_crdt.associativity
    with (initial := crdt.(state_crdt.initial)); search.
  rewrite state_crdt.commutativity
    with (initial := crdt.(state_crdt.initial)) (x := o1); search.
Qed.

(*
  We can emulate an operation-based CRDT with a state-based CRDT if the
  delivery precondition and equality on operations are decidable and there is a
  way to order any given set of operations. The order can be completely
  arbitrary.
*)

#[local] Obligation Tactic := auto. (* `search` diverges here, sadly. *)

Program Definition state_crdt_from_operation_crdt
  [A Q]
  [crdt_data : operation_crdt.CrdtData A Q]
  (crdt : operation_crdt.Crdt crdt_data)
  (precondition :
    forall s o,
    {crdt_data.(operation_crdt.Precondition) s o} +
    {~ crdt_data.(operation_crdt.Precondition) s o})
  (equal :
    forall (o1 o2 : crdt_data.(operation_crdt.Operation)),
    {o1 = o2} + {o1 <> o2})
  (permute :
    list crdt_data.(operation_crdt.Operation) ->
    list crdt_data.(operation_crdt.Operation))
  (H1 : forall os, Permutation os (permute os))
  (H : forall os1 os2, Permutation os1 os2 -> permute os1 = permute os2)
: state_crdt.Crdt A Q :=
  {|
    state_crdt.State :=
      list crdt_data.(operation_crdt.Operation) *
      list crdt_data.(operation_crdt.Operation);
    state_crdt.initial := ([], []);
    state_crdt.merge '(_, _) '(_, _) := _;
    state_crdt.update _ '(_, _) := _;
    state_crdt.query '(_, delivered) :=
      crdt_data.(operation_crdt.query)
        (operation_crdt.run crdt_data delivered);
  |}.
Next Obligation.
  clean.
  split; search.
Admitted.
Next Obligation.
Admitted.

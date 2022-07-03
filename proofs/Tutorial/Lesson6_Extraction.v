(**************************************)
(**************************************)
(****                              ****)
(****   Extracting verified code   ****)
(****                              ****)
(**************************************)
(**************************************)

(*************************************************)
(* Information cannot leave the `Prop` universe. *)
(*************************************************)

(*
  Everything in `Prop` is considered a proposition, and the inhabitants of
  those propositions are considered proofs. For example, the following
  proposition has two proofs:
*)

Inductive myProp : Prop :=
| proof1 : myProp
| proof2 : myProp.

(* Since `myProp` is an inductive type, it supports pattern matching. *)

Definition flipFlop (proof : myProp) : myProp :=
  match proof with
  | proof1 => proof2
  | proof2 => proof1
  end.

(*
  As we will see in this lesson, Coq code can be "extracted" into code in other
  languages such that the proofs are erased. But in order for extraction to
  make sense, it's important that none of the extracted code makes decisions
  based on the erased proofs. Coq guarantees this with a restriction on pattern
  matching. The following is rejected because the return type is not in `Prop`:
*)

Fail Definition myPropToNat (proof : myProp) : nat :=
  match proof with
  | proof1 => 0
  | proof2 => 1
  end.

(*
  ```
  The command has indeed failed with message:
  Incorrect elimination of "proof" in the inductive type "myProp":
  the return type has sort "Set" while it should be "SProp" or "Prop".
  Elimination of an inductive object of sort Prop
  is not allowed on a predicate in sort Set
  because proofs can be eliminated only to build proofs.
  ```

  However, if a proposition has zero constructors or one constructor for which
  the non-parameter arguments are proofs, then pattern matching on it doesn't
  result in any decisions being made based on the proof. Thus, Coq allows the
  following:
*)

Definition falseToNat (proof : False) : nat :=
  match proof with
  end.

Definition trueToNat (proof : True) : nat :=
  match proof with
  | I => 0
  end.

Definition falseAndTrueToNat (proof : False /\ True) : nat :=
  match proof with
  | conj _ _ => 0
  end.

Definition eqToNat (proof : false = false) : nat :=
  match proof with
  | eq_refl _ => 0
  end.

(*************************************)
(* Extracting verified code to OCaml *)
(*************************************)

(* This allows us to use Boolean operators such as `&&` and `||`. *)

#[local] Open Scope bool_scope.

(* Let's define an xor function and prove it correct. *)

Definition xor b1 b2 :=
  match (b1, b2) with
  | (true, true) => false
  | (false, false) => false
  | (true, false) => true
  | (false, true) => true
  end.

Theorem xor_correct : forall b1 b2, xor b1 b2 = (b1 || b2) && negb (b1 && b2).
Proof.
  intros.
  destruct b1; destruct b2; reflexivity.
Qed.

(* Now let's extract the code to OCaml. *)

From Coq Require Extraction.

Recursive Extraction xor.

(*
  ```
  type bool =
  | True
  | False

  (** val xor : bool -> bool -> bool **)

  let xor b1 b2 =
    match b1 with
    | True -> (match b2 with
               | True -> False
               | False -> True)
    | False -> b2
  ```

  This code works, but it would be better if `xor` took an OCaml `bool` rather
  than an extracted copy of it. We can tell Coq not to extract `bool` and
  instead any code which uses it will use OCaml's `bool`.
*)

Extract Inductive bool => "bool" [ "true" "false" ].

Recursive Extraction xor.

(*
  ```
  (** val xor : bool -> bool -> bool **)

  let xor b1 b2 =
    if b1 then if b2 then false else true else b2
  ```

  We've formally verified a function and extracted it to OCaml! In practice,
  we'd extract the code to a file to be fed to the OCaml compiler:

  ```
  Extraction "xor.ml" xor.
  ```
*)

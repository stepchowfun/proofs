(**************************************)
(**************************************)
(****                              ****)
(****   Extracting verified code   ****)
(****                              ****)
(**************************************)
(**************************************)

Require Import Coq.micromega.Lia.
From Coq Require Extraction.

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

(***************************************************)
(* Extracting a simple verified program to Haskell *)
(***************************************************)

Extraction Language Haskell.

(*
  For simple enumerated data types, we can simply give the translation of the
  type and its constructors.
*)

Extract Inductive bool => "Bool" [ "True" "False" ].

(*
  For inductive data types for which the constructors have arguments, we must
  also provide a function for pattern matching.
*)

Extract Inductive nat =>
  "Integer"
  [ "0" "(+1)" ]
  "(\zero succ n -> if n == 0 then zero () else succ (n - 1))".

(* We can also give translations for constants. *)

Extract Constant plus => "(+)".
Extract Constant mult => "(*)".

(*
  Let's write a simple program, prove it correct, and extract it to Haskell.
*)

Definition double x := x * 2.

Theorem doubleCorrect : forall x, double x = x + x.
Proof.
  unfold double.
  lia.
Qed.

Recursive Extraction double.

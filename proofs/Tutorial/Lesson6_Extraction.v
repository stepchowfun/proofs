(**************************************)
(**************************************)
(****                              ****)
(****   Extracting verified code   ****)
(****                              ****)
(**************************************)
(**************************************)

Require Import Extraction.
Require Import Lia.
Require Import Nat.

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
  Let's write a simple program with dependent types, prove it correct, and
  extract the computational part to Haskell.
*)

Definition double (x : nat) : {y : nat | even y = true }.
Proof.
  exists (x * 2).
  induction x; auto.
Defined.

Theorem double_correct : forall x, proj1_sig (double x) = x + x.
Proof.
  intro.
  cbn.
  lia.
Qed.

Recursive Extraction double.

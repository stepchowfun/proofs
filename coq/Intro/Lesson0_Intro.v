(****************************************************)
(****************************************************)
(****                                            ****)
(****   Ordinary functional programming in Coq   ****)
(****                                            ****)
(****************************************************)
(****************************************************)

(* Let's define a data type for Booleans. *)

Inductive bool : Set :=
| true : bool
| false : bool.

(* The `Check` command tells us the type of a given term. *)

Check true. (* bool *)
Check false. (* bool *)

(* Here's a simple function on Bools. *)

Definition negb b :=
  match b with
  | true => false
  | false => true
  end.

(* Let's compute some examples. *)

Compute negb true. (* false *)
Compute negb false. (* true *)

(*
  Here's a more interesting inductive data type: a natural number is either
  zero or the successor of another natural number.
*)

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

(* Here are some natural numbers: *)

Check O. (* nat *)
Check S O. (* nat *)
Check S (S O). (* nat *)

(* Numeric literals can also be used to construct natural numbers. *)

Check 0. (* Datatypes.nat *)
Check 1. (* Datatypes.nat *)
Check 2. (* Datatypes.nat *)

(*
  Recursive definitions use the `Fixpoint` keyword instead of `Definition`.
*)

Fixpoint add n m :=
  match n with
  | O => m
  | S p => S (add p m)
  end.

(* Let's compute 1 + 1. *)

Compute add (S O) (S O). (* S (S O) *)

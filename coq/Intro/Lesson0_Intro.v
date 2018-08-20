(******************************************)
(* Ordinary functional programming in Coq *)
(******************************************)

(*
  Let's define a data type for Booleans.
  In Haskell, we'd write:

    data Bool = True | False

  Haskell also lets us define this as a
  GADT, which will look similar to the
  Coq definition:

    data Bool where
      True :: Bool
      False :: Bool
*)

Inductive bool : Set :=
| true : bool
| false : bool.

(*
  Here's a more interesting example of
  an inductive data type. In Haskell:

    data Nat = Zero | Succ Nat
*)

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

(*
  The `Check` command tells us the type
  of a given term.
*)

Check O.
Check S O.
Check S (S O).

(*
  Here's a simple function. In Haskell:

    negb :: Bool -> Bool
    negb True = False
    negb False = True
*)

Definition negb b :=
  match b with
  | true => false
  | false => true
  end.

(* Let's compute some examples. *)

Compute negb true.
Compute negb false.

(*
  Recursive definitions use the `Fixpoint`
  keyword instead of `Definition`.
*)

Fixpoint add n m :=
  match n with
  | O => m
  | S p => S (add p m)
  end.

(* Let's compute 1 + 1. *)

Compute add (S O) (S O).

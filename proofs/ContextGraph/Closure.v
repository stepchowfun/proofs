(******************************************)
(******************************************)
(****                                  ****)
(****   Transitive reflexive closure   ****)
(****                                  ****)
(******************************************)
(******************************************)

Require Import Main.Tactics.

(*
  This is the transitive reflexive closure of a given relation. Reflexivity is
  immediate from the definition, and transitivity is proven below.
*)

Inductive closure {T : Type} (R : T -> T -> Prop) (x : T) : T -> Prop :=
| reflexivity : closure R x x
| extension : forall y z, closure R x y -> R y z -> closure R x z.

#[export] Hint Constructors closure : main.

Theorem transitivity :
  forall (T : Type) (R : T -> T -> Prop) (x y z : T),
  closure R x y ->
  closure R y z ->
  closure R x z.
Proof.
  clean.
  induction H0; eMagic.
Qed.

#[export] Hint Resolve transitivity : main.

Theorem completeness :
  forall (T : Type) (R : T -> T -> Prop) (x y : T),
  R x y ->
  closure R x y.
Proof.
  eMagic.
Qed.

#[export] Hint Resolve completeness : main.

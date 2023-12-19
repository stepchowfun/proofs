(******************************)
(******************************)
(****                      ****)
(****   Terminal objects   ****)
(****                      ****)
(******************************)
(******************************)

Require Import Coq.Classes.Morphisms.
Require Import main.category_theory.category.
Require Import main.category_theory.initial.
Require Import main.category_theory.object.
Require Import main.tactics.

#[local] Set Universe Polymorphism.

Definition terminal [C] (x : Object C) :=
  forall y, exists f, forall (g : Arrow y x), f = g.

Theorem op_initial_terminal [C] x :
  @initial C x <-> @terminal (opposite_category C) x.
Proof.
  search.
Qed.

#[export] Hint Resolve op_initial_terminal : main.

Theorem op_terminal_initial [C] x :
  @terminal C x <-> @initial (opposite_category C) x.
Proof.
  search.
Qed.

#[export] Hint Resolve op_terminal_initial : main.

Theorem terminal_unique C : UniqueUpToIsomorphism (@terminal C).
Proof.
  unfold UniqueUpToIsomorphism.
  clean.
  rewrite op_terminal_initial in *.
  rewrite op_isomorphic.
  apply initial_unique; search.
Qed.

#[export] Hint Resolve terminal_unique : main.

(********************)
(********************)
(****            ****)
(****   Arrows   ****)
(****            ****)
(********************)
(********************)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.
Require Import main.category_theory.category.
Require Import main.tactics.

#[local] Set Universe Polymorphism.

Definition endomorphism [C] x := @Arrow C x x.

Definition ArrowExists [C] [x y : Object C] (P : Arrow x y -> Prop) :=
  exists f, P f.

Definition ArrowUnique [C] [x y : Object C] (P : Arrow x y -> Prop) :=
  forall f g, P f -> P g -> f = g.

Definition Universal [C] [x y : Object C] (P : Arrow x y -> Prop) :=
  ArrowExists P /\ ArrowUnique P.

Definition Inverse [C] [x y : Object C] (f : Arrow x y) (g : Arrow y x) :=
  compose f g = id x /\ compose g f = id y.

Definition Epimorphism [C] [x y : Object C] (f : Arrow x y) :=
  forall z (g h : Arrow y z), compose f g = compose f h -> g = h.

Definition Monomorphism [C] [x y : Object C] (f : Arrow x y) :=
  forall z (g h : Arrow z x), compose g f = compose h f -> g = h.

Definition Isomorphism [C] [x y : Object C] (f : Arrow x y) :=
  exists g, Inverse f g.

Definition Automorphism [C] [x : Object C] (f : endomorphism x) :=
  Isomorphism f.

Definition Retraction [C] [x y : Object C] (f : Arrow x y) :=
  exists g, compose g f = id y.

Definition Section [C] [x y : Object C] (f : Arrow x y) :=
  exists g, compose f g = id x.

Theorem op_isomorphism [C x y] f :
  @Isomorphism C x y f <-> @Isomorphism (opposite_category C) y x f.
Proof.
  unfold Isomorphism.
  unfold Inverse.
  split; clean; exists x0; search.
Qed.

Hint Resolve op_isomorphism : main.

Theorem op_mono_epi [C x y] f :
  @Monomorphism C x y f <-> @Epimorphism (opposite_category C) y x f.
Proof.
  search.
Qed.

Hint Resolve op_mono_epi : main.

Theorem op_epi_mono [C x y] f :
  @Epimorphism C x y f <-> @Monomorphism (opposite_category C) y x f.
Proof.
  search.
Qed.

Hint Resolve op_epi_mono : main.

Theorem op_ret_sec [C x y] f :
  @Retraction C x y f <-> @Section (opposite_category C) y x f.
Proof.
  search.
Qed.

Hint Resolve op_ret_sec : main.

Theorem op_sec_ret [C x y] f :
  @Section C x y f <-> @Retraction (opposite_category C) y x f.
Proof.
  search.
Qed.

Hint Resolve op_sec_ret : main.

Theorem id_iso [C] x : Isomorphism (@id C x).
Proof.
  unfold Isomorphism.
  exists (id x).
  unfold Inverse.
  search.
Qed.

Hint Resolve id_iso : main.

Theorem left_id_unique [C] (x : Object C):
  ArrowUnique (
    fun (f : Arrow x x) => forall y (g : Arrow x y), compose f g = g
  ).
Proof.
  unfold ArrowUnique.
  clean.
  specialize (H x (id x)).
  specialize (H0 x (id x)).
  search.
Qed.

Hint Resolve left_id_unique : main.

Theorem right_id_unique [C] (x : Object C):
  ArrowUnique (
    fun (f : Arrow x x) => forall y (g : Arrow y x), compose g f = g
  ).
Proof.
  unfold ArrowUnique.
  clean.
  specialize (H x (id x)).
  specialize (H0 x (id x)).
  search.
Qed.

Hint Resolve right_id_unique : main.

Theorem inverse_unique [C] [x y : Object C] (f : Arrow x y) :
  ArrowUnique (Inverse f).
Proof.
  unfold ArrowUnique.
  unfold Inverse.
  clean.
  assert (compose f0 (compose f g) = compose (compose f0 f) g); search.
  rewrite H0 in H3.
  rewrite H2 in H3.
  search.
Qed.

Hint Resolve inverse_unique : main.

Theorem inverse_involution [C] [x y : Object C] (f h : Arrow x y) g :
  Inverse f g -> Inverse g h -> f = h.
Proof.
  unfold Inverse.
  clean.
  assert (f = compose f (compose g h)).
  - rewrite H0. search.
  - assert (h = compose f (compose g h)); search.
    rewrite <- c_assoc. rewrite H. search.
Qed.

Hint Resolve inverse_involution : main.

Theorem iso_implies_epi [C x y] f :
  @Isomorphism C x y f -> @Epimorphism C x y f.
Proof.
  unfold Isomorphism.
  unfold Epimorphism.
  unfold Inverse.
  clean.
  assert (
    compose x0 (compose f g) = compose x0 (compose f h)
  ); search.
  repeat rewrite <- c_assoc in H2.
  repeat rewrite H1 in H2.
  search.
Qed.

Hint Resolve iso_implies_epi : main.

Theorem iso_implies_mono [C x y] f :
  @Isomorphism C x y f -> @Monomorphism C x y f.
Proof.
  clean.
  rewrite op_mono_epi.
  apply iso_implies_epi.
  rewrite <- op_isomorphism.
  search.
Qed.

Hint Resolve iso_implies_mono : main.

Theorem sec_implies_mono [C x y] f : @Section C x y f -> @Monomorphism C x y f.
Proof.
  unfold Section.
  unfold Monomorphism.
  clean.
  assert (
    compose (compose g f) x0 = compose (compose h f) x0
  ); search.
  repeat rewrite c_assoc in H1.
  repeat rewrite H in H1.
  search.
Qed.

Hint Resolve sec_implies_mono : main.

Theorem ret_implies_epi [C x y] f :
  @Retraction C x y f -> @Epimorphism C x y f.
Proof.
  clean.
  rewrite op_ret_sec in H.
  rewrite op_epi_mono.
  search.
Qed.

Hint Resolve ret_implies_epi : main.

Theorem mono_ret_equiv_iso [C x y] f :
  @Monomorphism C x y f /\ @Retraction C x y f <-> @Isomorphism C x y f.
Proof.
  unfold Monomorphism.
  unfold Retraction.
  unfold Isomorphism.
  unfold Inverse.
  split; clean.
  - exists x0.
    split; search.
    specialize (H x (compose f x0) (id x)).
    feed H.
    rewrite c_assoc.
    rewrite H0.
    search.
  - split; esearch.
    clean.
    assert (
      compose (compose g f) x0 = compose (compose h f) x0
    ); search.
    repeat rewrite c_assoc in H2.
    rewrite H in H2.
    search.
Qed.

Hint Resolve mono_ret_equiv_iso : main.

Theorem epi_sec_equiv_iso [C x y] f :
  @Epimorphism C x y f /\ @Section C x y f <-> @Isomorphism C x y f.
Proof.
  clean.
  rewrite op_epi_mono.
  rewrite op_sec_ret.
  rewrite op_isomorphism.
  search.
Qed.

Hint Resolve epi_sec_equiv_iso : main.

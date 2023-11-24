(********************)
(********************)
(****            ****)
(****   Arrows   ****)
(****            ****)
(********************)
(********************)

Require Import Coq.Classes.Morphisms.
Require Import Coq.Classes.Morphisms_Prop.
Require Import Main.CategoryTheory.Category.
Require Import Main.Tactics.

#[local] Set Universe Polymorphism.

Definition endomorphism [C] x := @arrow C x x.

Definition arrowExists [C] [x y : object C] (P : arrow x y -> Prop) :=
  exists f, P f.

Definition arrowUnique [C] [x y : object C] (P : arrow x y -> Prop) :=
  forall f g, P f -> P g -> f = g.

Definition universal [C] [x y : object C] (P : arrow x y -> Prop) :=
  arrowExists P /\ arrowUnique P.

Definition inverse [C] [x y : object C] (f : arrow x y) (g : arrow y x) :=
  compose f g = id x /\ compose g f = id y.

Definition epimorphism [C] [x y : object C] (f : arrow x y) :=
  forall z (g h : arrow y z), compose f g = compose f h -> g = h.

Definition monomorphism [C] [x y : object C] (f : arrow x y) :=
  forall z (g h : arrow z x), compose g f = compose h f -> g = h.

Definition isomorphism [C] [x y : object C] (f : arrow x y) :=
  exists g, inverse f g.

Definition automorphism [C] [x : object C] (f : endomorphism x) :=
  isomorphism f.

Definition retraction [C] [x y : object C] (f : arrow x y) :=
  exists g, compose g f = id y.

Definition section [C] [x y : object C] (f : arrow x y) :=
  exists g, compose f g = id x.

Theorem opIsomorphism [C x y] f :
  @isomorphism C x y f <-> @isomorphism (oppositeCategory C) y x f.
Proof.
  unfold isomorphism.
  unfold inverse.
  split; clean; exists x0; search.
Qed.

#[export] Hint Resolve opIsomorphism : main.

Theorem opMonoEpi [C x y] f :
  @monomorphism C x y f <-> @epimorphism (oppositeCategory C) y x f.
Proof.
  search.
Qed.

#[export] Hint Resolve opMonoEpi : main.

Theorem opEpiMono [C x y] f :
  @epimorphism C x y f <-> @monomorphism (oppositeCategory C) y x f.
Proof.
  search.
Qed.

#[export] Hint Resolve opEpiMono : main.

Theorem opRetSec [C x y] f :
  @retraction C x y f <-> @section (oppositeCategory C) y x f.
Proof.
  search.
Qed.

#[export] Hint Resolve opRetSec : main.

Theorem opSecRet [C x y] f :
  @section C x y f <-> @retraction (oppositeCategory C) y x f.
Proof.
  search.
Qed.

#[export] Hint Resolve opSecRet : main.

Theorem idIso [C] x : isomorphism (@id C x).
Proof.
  unfold isomorphism.
  exists (id x).
  unfold inverse.
  search.
Qed.

#[export] Hint Resolve idIso : main.

Theorem leftIdUnique [C] (x : object C):
  arrowUnique (
    fun (f : arrow x x) => forall y (g : arrow x y), compose f g = g
  ).
Proof.
  unfold arrowUnique.
  clean.
  specialize (H x (id x)).
  specialize (H0 x (id x)).
  search.
Qed.

#[export] Hint Resolve leftIdUnique : main.

Theorem rightIdUnique [C] (x : object C):
  arrowUnique (
    fun (f : arrow x x) => forall y (g : arrow y x), compose g f = g
  ).
Proof.
  unfold arrowUnique.
  clean.
  specialize (H x (id x)).
  specialize (H0 x (id x)).
  search.
Qed.

#[export] Hint Resolve rightIdUnique : main.

Theorem inverseUnique [C] [x y : object C] (f : arrow x y) :
  arrowUnique (inverse f).
Proof.
  unfold arrowUnique.
  unfold inverse.
  clean.
  assert (compose f0 (compose f g) = compose (compose f0 f) g); search.
  rewrite H0 in H3.
  rewrite H2 in H3.
  search.
Qed.

#[export] Hint Resolve inverseUnique : main.

Theorem inverseInvolution [C] [x y : object C] (f h : arrow x y) g :
  inverse f g -> inverse g h -> f = h.
Proof.
  unfold inverse.
  clean.
  assert (f = compose f (compose g h)).
  - rewrite H0. search.
  - assert (h = compose f (compose g h)); search.
    rewrite <- cAssoc. rewrite H. search.
Qed.

#[export] Hint Resolve inverseInvolution : main.

Theorem isoImpliesEpi [C x y] f : @isomorphism C x y f -> @epimorphism C x y f.
Proof.
  unfold isomorphism.
  unfold epimorphism.
  unfold inverse.
  clean.
  assert (
    compose x0 (compose f g) = compose x0 (compose f h)
  ); search.
  repeat rewrite <- cAssoc in H2.
  repeat rewrite H1 in H2.
  search.
Qed.

#[export] Hint Resolve isoImpliesEpi : main.

Theorem isoImpliesMono [C x y] f :
  @isomorphism C x y f -> @monomorphism C x y f.
Proof.
  clean.
  rewrite opMonoEpi.
  apply isoImpliesEpi.
  rewrite <- opIsomorphism.
  search.
Qed.

#[export] Hint Resolve isoImpliesMono : main.

Theorem secImpliesMono [C x y] f : @section C x y f -> @monomorphism C x y f.
Proof.
  unfold section.
  unfold monomorphism.
  clean.
  assert (
    compose (compose g f) x0 = compose (compose h f) x0
  ); search.
  repeat rewrite cAssoc in H1.
  repeat rewrite H in H1.
  search.
Qed.

#[export] Hint Resolve secImpliesMono : main.

Theorem retImpliesEpi [C x y] f : @retraction C x y f -> @epimorphism C x y f.
Proof.
  clean.
  rewrite opRetSec in H.
  rewrite opEpiMono.
  search.
Qed.

#[export] Hint Resolve retImpliesEpi : main.

Theorem monoRetEquivIso [C x y] f :
  @monomorphism C x y f /\ @retraction C x y f <-> @isomorphism C x y f.
Proof.
  unfold monomorphism.
  unfold retraction.
  unfold isomorphism.
  unfold inverse.
  split; clean.
  - exists x0.
    split; search.
    specialize (H x (compose f x0) (id x)).
    feed H.
    rewrite cAssoc.
    rewrite H0.
    search.
  - split; eSearch.
    clean.
    assert (
      compose (compose g f) x0 = compose (compose h f) x0
    ); search.
    repeat rewrite cAssoc in H2.
    rewrite H in H2.
    search.
Qed.

#[export] Hint Resolve monoRetEquivIso : main.

Theorem epiSecEquivIso [C x y] f :
  @epimorphism C x y f /\ @section C x y f <-> @isomorphism C x y f.
Proof.
  clean.
  rewrite opEpiMono.
  rewrite opSecRet.
  rewrite opIsomorphism.
  search.
Qed.

#[export] Hint Resolve epiSecEquivIso : main.

(********************)
(********************)
(****            ****)
(****   Arrows   ****)
(****            ****)
(********************)
(********************)

Require Import Main.CategoryTheory.Category.
Require Import Main.Tactics.

Set Universe Polymorphism.

Definition endomorphism {C} x := @arrow C x x.

Definition arrowExists {C} {x y : object C} (P : arrow x y -> Prop) :=
  exists f, P f.

Definition arrowUnique {C} {x y : object C} (P : arrow x y -> Prop) :=
  forall f g, P f -> P g -> f = g.

Definition universal {C} {x y : object C} (P : arrow x y -> Prop) :=
  arrowExists P /\ arrowUnique P.

Definition inverse {C} {x y : object C} (f : arrow x y) (g : arrow y x) :=
  compose f g = id /\ compose g f = id.

Definition epimorphism {C} {x y : object C} (f : arrow x y) :=
  forall z (g h : arrow y z), compose g f = compose h f -> g = h.

Definition monomorphism {C} {x y : object C} (f : arrow x y) :=
  forall z (g h : arrow z x), compose f g = compose f h -> g = h.

Definition isomorphism {C} {x y : object C} (f : arrow x y) :=
  exists g, inverse f g.

Definition automorphism {C} {x : object C} (f : endomorphism x) :=
  isomorphism f.

Definition retraction {C} {x y : object C} (f : arrow x y) :=
  exists g, compose f g = id.

Definition section {C} {x y : object C} (f : arrow x y) :=
  exists g, compose g f = id.

Theorem opIsomorphism C x y f :
  @isomorphism C x y f <-> @isomorphism (oppositeCategory C) y x f.
Proof.
  unfold isomorphism.
  unfold inverse.
  split; clean; exists x0; magic.
Qed.

#[export] Hint Resolve opIsomorphism : core.

Theorem opMonoEpi C x y f :
  @monomorphism C x y f <-> @epimorphism (oppositeCategory C) y x f.
Proof.
  magic.
Qed.

#[export] Hint Resolve opMonoEpi : core.

Theorem opEpiMono C x y f :
  @epimorphism C x y f <-> @monomorphism (oppositeCategory C) y x f.
Proof.
  magic.
Qed.

#[export] Hint Resolve opEpiMono : core.

Theorem opRetSec C x y f :
  @retraction C x y f <-> @section (oppositeCategory C) y x f.
Proof.
  magic.
Qed.

#[export] Hint Resolve opRetSec : core.

Theorem opSecRet C x y f :
  @section C x y f <-> @retraction (oppositeCategory C) y x f.
Proof.
  magic.
Qed.

#[export] Hint Resolve opSecRet : core.

Theorem idIso C x : isomorphism (@id C x).
Proof.
  unfold isomorphism.
  exists id.
  unfold inverse.
  magic.
Qed.

#[export] Hint Resolve idIso : core.

Theorem rightIdUnique C (x : object C):
  arrowUnique (
    fun (f : arrow x x) => forall y (g : arrow x y), compose g f = g
  ).
Proof.
  unfold arrowUnique.
  clean.
  specialize (H x id).
  specialize (H0 x id).
  magic.
Qed.

#[export] Hint Resolve rightIdUnique : core.

Theorem leftIdUnique C (x : object C):
  arrowUnique (
    fun (f : arrow x x) => forall y (g : arrow y x), compose f g = g
  ).
Proof.
  unfold arrowUnique.
  clean.
  specialize (H x id).
  specialize (H0 x id).
  magic.
Qed.

#[export] Hint Resolve leftIdUnique : core.

Theorem inverseUnique C (x y : object C) (f : arrow x y) :
  arrowUnique (inverse f).
Proof.
  unfold arrowUnique.
  unfold inverse.
  clean.
  assert (compose f0 (compose f g) = compose (compose f0 f) g); magic.
  rewrite H0 in H3.
  rewrite H2 in H3.
  magic.
Qed.

#[export] Hint Resolve inverseUnique : core.

Theorem inverseInvolution C (x y : object C) (f h : arrow x y) g :
  inverse f g -> inverse g h -> f = h.
Proof.
  unfold inverse.
  clean.
  assert (f = compose f (compose g h)).
  - rewrite H0. magic.
  - assert (h = compose f (compose g h)); magic.
    rewrite cAssoc. rewrite H. magic.
Qed.

#[export] Hint Resolve inverseInvolution : core.

Theorem isoImpliesEpi C x y f : @isomorphism C x y f -> @epimorphism C x y f.
Proof.
  unfold isomorphism.
  unfold epimorphism.
  unfold inverse.
  clean.
  assert (
    compose (compose g f) x0 = compose (compose h f) x0
  ); magic.
  repeat rewrite <- cAssoc in H2.
  repeat rewrite H in H2.
  magic.
Qed.

#[export] Hint Resolve isoImpliesEpi : core.

Theorem isoImpliesMono C x y f : @isomorphism C x y f -> @monomorphism C x y f.
Proof.
  clean.
  rewrite opMonoEpi.
  apply isoImpliesEpi.
  rewrite <- opIsomorphism.
  magic.
Qed.

#[export] Hint Resolve isoImpliesMono : core.

Theorem secImpliesMono C x y f : @section C x y f -> @monomorphism C x y f.
Proof.
  unfold section.
  unfold monomorphism.
  clean.
  assert (
    compose x0 (compose f g) = compose x0 (compose f h)
  ); magic.
  repeat rewrite cAssoc in H1.
  repeat rewrite H in H1.
  magic.
Qed.

#[export] Hint Resolve secImpliesMono : core.

Theorem retImpliesEpi C x y f : @retraction C x y f -> @epimorphism C x y f.
Proof.
  clean.
  rewrite opRetSec in H.
  rewrite opEpiMono.
  magic.
Qed.

#[export] Hint Resolve retImpliesEpi : core.

Theorem monoRetEquivIso C x y f :
  @monomorphism C x y f /\ @retraction C x y f <-> @isomorphism C x y f.
Proof.
  unfold monomorphism.
  unfold retraction.
  unfold isomorphism.
  unfold inverse.
  split; clean.
  - exists x0.
    split; magic.
    specialize (H x (compose x0 f) id).
    feed H.
    rewrite cAssoc.
    rewrite H0.
    magic.
  - split; eMagic.
    clean.
    assert (
      compose x0 (compose f g) = compose x0 (compose f h)
    ); magic.
    repeat rewrite cAssoc in H2.
    rewrite H0 in H2.
    magic.
Qed.

#[export] Hint Resolve monoRetEquivIso : core.

Theorem epiSecEquivIso C x y f :
  @epimorphism C x y f /\ @section C x y f <-> @isomorphism C x y f.
Proof.
  clean.
  rewrite opEpiMono.
  rewrite opSecRet.
  rewrite opIsomorphism.
  magic.
Qed.

#[export] Hint Resolve epiSecEquivIso : core.

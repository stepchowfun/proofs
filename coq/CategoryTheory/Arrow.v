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

(* Arrows *)

Definition arrowExists {C : category} {x y} (P : arrow C x y -> Prop) :=
  exists f, P f.

Definition arrowUnique {C : category} {x y} (P : arrow C x y -> Prop) :=
  forall f g, P f -> P g -> f = g.

Definition universal {C : category} {x y} (P : arrow C x y -> Prop) :=
  arrowExists P /\ arrowUnique P.

Definition epimorphism {C x y} (f : arrow C x y) :=
  forall z (g h : arrow C y z), compose C g f = compose C h f -> g = h.

Definition monomorphism {C x y} (f : arrow C x y) :=
  forall z (g h : arrow C z x), compose C f g = compose C f h -> g = h.

Definition isomorphism {C x y} (f : arrow C x y) :=
  exists g, compose C g f = id C /\ compose C f g = id C.

Definition retraction {C x y} (f : arrow C x y) :=
  exists g, compose C f g = id C.

Definition section {C x y} (f : arrow C x y) :=
  exists g, compose C g f = id C.

Theorem opIsomorphism :
  forall C x y f,
  @isomorphism C x y f <-> @isomorphism (oppositeCategory C) y x f.
Proof.
  unfold isomorphism.
  split; clean; exists x0; magic.
Qed.

Hint Resolve opIsomorphism.

Theorem opMonoEpi :
  forall C x y f,
  @monomorphism C x y f <-> @epimorphism (oppositeCategory C) y x f.
Proof.
  magic.
Qed.

Hint Resolve opMonoEpi.

Theorem opEpiMono :
  forall C x y f,
  @epimorphism C x y f <-> @monomorphism (oppositeCategory C) y x f.
Proof.
  magic.
Qed.

Hint Resolve opEpiMono.

Theorem opRetSec :
  forall C x y f,
  @retraction C x y f <-> @section (oppositeCategory C) y x f.
Proof.
  magic.
Qed.

Hint Resolve opRetSec.

Theorem opSecRet :
  forall C x y f,
  @section C x y f <-> @retraction (oppositeCategory C) y x f.
Proof.
  magic.
Qed.

Hint Resolve opSecRet.

Theorem rightIdUnique :
  forall C x, arrowUnique (
    fun (f : arrow C x x) => forall y (g : arrow C x y), compose C g f = g
  ).
Proof.
  unfold arrowUnique.
  clean.
  specialize (H x (id C)).
  specialize (H0 x (id C)).
  magic.
Qed.

Hint Resolve rightIdUnique.

Theorem leftIdUnique :
  forall C x, arrowUnique (
    fun (f : arrow C x x) => forall y (g : arrow C y x), compose C f g = g
  ).
Proof.
  unfold arrowUnique.
  clean.
  specialize (H x (id C)).
  specialize (H0 x (id C)).
  magic.
Qed.

Hint Resolve leftIdUnique.

Theorem inverseUnique {C x y} (f : arrow C x y) :
  arrowUnique (fun g => compose C f g = id C /\ compose C g f = id C).
Proof.
  unfold arrowUnique.
  clean.
  assert (compose C f0 (compose C f g) = compose C (compose C f0 f) g); magic.
  rewrite H0 in H3.
  rewrite H2 in H3.
  magic.
Qed.

Hint Resolve inverseUnique.

Theorem isoImpliesEpi :
  forall C x y f, @isomorphism C x y f -> @epimorphism C x y f.
Proof.
  unfold isomorphism.
  unfold epimorphism.
  clean.
  assert (
    compose C (compose C g f) x0 = compose C (compose C h f) x0
  ); magic.
  repeat rewrite <- cAssoc in H2.
  repeat rewrite H1 in H2.
  magic.
Qed.

Hint Resolve isoImpliesEpi.

Theorem isoImpliesMono :
  forall C x y f, @isomorphism C x y f -> @monomorphism C x y f.
Proof.
  clean.
  rewrite opMonoEpi.
  apply isoImpliesEpi.
  rewrite <- opIsomorphism.
  magic.
Qed.

Hint Resolve isoImpliesMono.

Theorem secImpliesMono :
  forall C x y f, @section C x y f -> @monomorphism C x y f.
Proof.
  unfold section.
  unfold monomorphism.
  clean.
  assert (
    compose C x0 (compose C f g) = compose C x0 (compose C f h)
  ); magic.
  repeat rewrite cAssoc in H1.
  repeat rewrite H in H1.
  magic.
Qed.

Hint Resolve secImpliesMono.

Theorem retImpliesEpi :
  forall C x y f, @retraction C x y f -> @epimorphism C x y f.
Proof.
  clean.
  rewrite opRetSec in H.
  rewrite opEpiMono.
  magic.
Qed.

Hint Resolve retImpliesEpi.

Theorem monoRetEquivIso :
  forall C x y f,
  @monomorphism C x y f /\ @retraction C x y f <-> @isomorphism C x y f.
Proof.
  unfold monomorphism.
  unfold retraction.
  unfold isomorphism.
  split; clean.
  - exists x0.
    split; magic.
    specialize (H x (compose C x0 f) (id C)).
    feed H.
    rewrite cAssoc.
    rewrite H0.
    magic.
  - split; eMagic.
    clean.
    assert (
      compose C x0 (compose C f g) = compose C x0 (compose C f h)
    ); magic.
    repeat rewrite cAssoc in H2.
    rewrite H in H2.
    magic.
Qed.

Hint Resolve monoRetEquivIso.

Theorem epiSecEquivIso :
  forall C x y f,
  @epimorphism C x y f /\ @section C x y f <-> @isomorphism C x y f.
Proof.
  clean.
  rewrite opEpiMono.
  rewrite opSecRet.
  rewrite opIsomorphism.
  magic.
Qed.

Hint Resolve epiSecEquivIso.

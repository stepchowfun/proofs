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

Definition arrowExistsUnique {C : category} {x y} (P : arrow C x y -> Prop) :=
  arrowExists P /\ arrowUnique P.

Definition epimorphism {C x y} (f : arrow C x y) :=
  forall z (g h : arrow C y z), compose C g f = compose C h f -> g = h.

Definition monomorphism {C x y} (f : arrow C x y) :=
  forall z (g h : arrow C z x), compose C f g = compose C f h -> g = h.

Definition isomorphism {C x y} (f : arrow C x y) :=
  exists g, compose C g f = id C /\ compose C f g = id C.

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
  unfold isomorphism.
  unfold monomorphism.
  clean.
  assert (
    compose C x0 (compose C f g) = compose C x0 (compose C f h)
  ); magic.
  repeat rewrite cAssoc in H2.
  repeat rewrite H in H2.
  magic.
Qed.

Hint Resolve isoImpliesMono.

Theorem opIso :
  forall C x y,
  (exists f, @isomorphism C x y f) <->
  (exists f, @isomorphism (oppositeCategory C) x y f).
Proof.
  unfold isomorphism; split; clean; exists x1; eMagic.
Qed.

Hint Resolve opIso.

(************************)
(************************)
(****                ****)
(****   Categories   ****)
(****                ****)
(************************)
(************************)

Require Import Main.Tactics.

Set Universe Polymorphism.

(* Metavariables for categories: C, D, E *)

Record category := newCategory {
  object : Type; (* Metavariables for objects: w, x, y, z *)
  arrow : object -> object -> Type; (* Metavariables for arrows: f, g, h *)
  compose : forall {x y z}, arrow y z -> arrow x y -> arrow x z;
  id : forall {x}, arrow x x;

  cAssoc :
    forall w x y z (f : arrow w x) (g : arrow x y) (h : arrow y z),
    compose h (compose g f) = compose (compose h g) f;
  cIdentLeft : forall x y (f : arrow x y), compose id f = f;
  cIdentRight : forall x y (f : arrow x y), compose f id = f;
}.

Hint Resolve cAssoc.
Hint Resolve cIdentLeft.
Hint Resolve cIdentRight.
Hint Rewrite cAssoc.
Hint Rewrite cIdentLeft.
Hint Rewrite cIdentRight.

Definition opCategory (C : category) : @category.
Proof.
  refine (newCategory
    (object C)
    (fun x y => arrow C y x)
    (fun {x y z} f g => compose C g f)
    (fun {x} => id C)
    _ _ _
  ); magic.
Defined.

Definition thin (C : category) :=
  forall x y (f g : arrow C x y), f = g.

(* Morphisms *)

Definition epimorphism {C x y} (f : arrow C x y) :=
  forall z (g h : arrow C y z), compose C g f = compose C h f -> g = h.

Definition monomorphism {C x y} (f : arrow C x y) :=
  forall z (g h : arrow C z x), compose C f g = compose C f h -> g = h.

Definition isomorphism {C x y} (f : arrow C x y) :=
  exists g, compose C f g = id C /\ compose C g f = id C.

Theorem isoImpliesEpi :
  forall C x y f, @isomorphism C x y f -> @epimorphism C x y f.
Proof.
  unfold isomorphism.
  unfold epimorphism.
  intros C x y f H z g h H0.
  destruct H as [fInv H]; destruct H.
  assert (
    compose C (compose C g f) fInv = compose C (compose C h f) fInv
  ) as H2; magic; clear H0.
  repeat rewrite <- cAssoc in H2.
  repeat rewrite H in H2.
  magic.
Qed.

Theorem isoImpliesMono :
  forall C x y f, @isomorphism C x y f -> @monomorphism C x y f.
Proof.
  unfold isomorphism.
  unfold monomorphism.
  intros C x y f H z g h H0.
  destruct H as [fInv H]; destruct H.
  assert (
    compose C fInv (compose C f g) = compose C fInv (compose C f h)
  ) as H2; magic; clear H0.
  repeat rewrite cAssoc in H2.
  repeat rewrite H1 in H2.
  magic.
Qed.

Hint Resolve isoImpliesEpi.
Hint Resolve isoImpliesMono.

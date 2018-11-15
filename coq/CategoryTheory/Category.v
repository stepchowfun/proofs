(************************)
(************************)
(****                ****)
(****   Categories   ****)
(****                ****)
(************************)
(************************)

Require Import Main.Tactics.
Require Import ProofIrrelevance.

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
Hint Rewrite cIdentLeft.
Hint Resolve cIdentRight.
Hint Rewrite cIdentRight.

Definition oppositeCategory (C : category) : category.
Proof.
  refine (newCategory
    (object C)
    (fun x y => arrow C y x)
    (fun {x y z} f g => compose C g f)
    (fun {x} => id C)
    _ _ _
  ); magic.
Defined.

Section ProofIrrelevance.
  Hint Resolve proof_irrelevance.

  Theorem oppositeInvolution :
    forall C, oppositeCategory (oppositeCategory C) = C.
  Proof.
    unfold oppositeCategory.
    clean.
    destruct C.
    magic.
  Qed.
End ProofIrrelevance.

Hint Resolve oppositeInvolution.

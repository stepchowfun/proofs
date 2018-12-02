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
  compose {x y z} : arrow y z -> arrow x y -> arrow x z;
  id {x}: arrow x x;

  cAssoc w x y z (f : arrow w x) (g : arrow x y) (h : arrow y z) :
    compose h (compose g f) = compose (compose h g) f;
  cIdentLeft x y (f : arrow x y) : compose id f = f;
  cIdentRight x y (f : arrow x y) : compose f id = f;
}.

Hint Resolve cAssoc.
Hint Resolve cIdentLeft.
Hint Rewrite cIdentLeft.
Hint Resolve cIdentRight.
Hint Rewrite cIdentRight.

Let opCAssoc
  {C : category}
  (w x y z : object C)
  (f : arrow C x w)
  (g : arrow C y x)
  (h : arrow C z y)
: compose C (compose C f g) h = compose C f (compose C g h).
Proof.
  magic.
Qed.

Let opCIdentLeft {C : category} (x y : object C) (f : arrow C y x) :
  compose C f (id C) = f.
Proof.
  magic.
Qed.

Let opCIdentRight {C : category} (x y : object C) (f : arrow C y x) :
  compose C (id C) f = f.
Proof.
  magic.
Qed.

Definition oppositeCategory (C : category) : category := newCategory
  (object C)
  (fun x y => arrow C y x)
  (fun {x y z} f g => compose C g f)
  (fun {x} => id C)
  opCAssoc
  opCIdentLeft
  opCIdentRight.

Theorem oppositeInvolution C : oppositeCategory (oppositeCategory C) = C.
Proof.
  unfold oppositeCategory.
  destruct C.
  f_equal; apply proof_irrelevance.
Qed.

Hint Resolve oppositeInvolution.

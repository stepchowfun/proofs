(************************)
(************************)
(****                ****)
(****   Categories   ****)
(****                ****)
(************************)
(************************)

Require Import Main.Tactics.

(* Metavariables for categories: C, D, E *)

Polymorphic Record category := newCategory {
  object :> Type; (* Metavariables for objects: w, x, y, z *)
  arrow : object -> object -> Type; (* Metavariables for arrows: f, g, h *)
  compose : forall {x y z}, arrow y z -> arrow x y -> arrow x z;
  id : forall {x}, arrow x x;

  cAssoc :
    forall w x y z (f : arrow w x) (g : arrow x y) (h : arrow y z),
    compose h (compose g f) = compose (compose h g) f;
  cIdent :
    forall x y,
    (forall (f : arrow x y), compose id f = f) /\
    (forall (f : arrow y x), compose f id = f);
}.

Polymorphic Hint Resolve cAssoc.
Polymorphic Hint Resolve (fun C x y => proj1 (cIdent C x y)).
Polymorphic Hint Resolve (fun C x y => proj2 (cIdent C x y)).
Polymorphic Hint Rewrite cAssoc.
Polymorphic Hint Rewrite (fun C x y => proj1 (cIdent C x y)).
Polymorphic Hint Rewrite (fun C x y => proj2 (cIdent C x y)).

Definition opCategory (C : category) : @category.
Proof.
  refine (newCategory
    (object C)
    (fun x y => arrow C y x)
    (fun {x y z} f g => compose C g f)
    (fun {x} => id C)
    _ _
  ); magic.
Defined.

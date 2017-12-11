(************************)
(************************)
(****                ****)
(****   Categories   ****)
(****                ****)
(************************)
(************************)

(* Metavariables for categories: C, D, E *)

Record category := newCategory {
  object : Type; (* Metavariables for objects: w, x, y, z *)
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

Hint Resolve cAssoc.
Hint Resolve (fun C x y => proj1 (cIdent C x y)).
Hint Resolve (fun C x y => proj2 (cIdent C x y)).
Hint Rewrite cAssoc.
Hint Rewrite (fun C x y => proj1 (cIdent C x y)).
Hint Rewrite (fun C x y => proj2 (cIdent C x y)).

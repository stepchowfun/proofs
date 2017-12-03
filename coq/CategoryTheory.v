(******************************************************)
(******************************************************)
(****                                              ****)
(****   A formalization of some category theory.   ****)
(****                                              ****)
(******************************************************)
(******************************************************)

Module Type Category.
  Parameter Object : Set.
  Parameter Arrow : Object -> Object -> Set.
  Parameter compose : forall {X Y Z}, Arrow Y Z -> Arrow X Y -> Arrow X Z.
  Parameter id : forall {X}, Arrow X X.

  Axiom assoc :
    forall W X Y Z (f : Arrow W X) (g : Arrow X Y) (h : Arrow Y Z),
    compose h (compose g f) = compose h (compose g f).
  Axiom ident :
    forall X Y (f : Arrow X Y) (g : Arrow Y X),
    compose f id = f /\ compose id g = g.
End Category.

Module Type Functor (C D : Category).
  Parameter omap : C.Object -> D.Object.
  Parameter fmap : forall {X Y}, C.Arrow X Y -> D.Arrow (omap X) (omap Y).

  Axiom ident : forall X, fmap (@C.id X) = @D.id (omap X).
  Axiom comp :
    forall X Y Z (f : C.Arrow X Y) (g : C.Arrow Y Z),
    fmap (C.compose g f) = D.compose (fmap g) (fmap f).
End Functor.

Module Type NaturalTransformation (C D : Category) (F G : Functor C D).
  Parameter eta : forall X, D.Arrow (F.omap X) (G.omap X).

  Axiom commute :
    forall X Y (f : C.Arrow X Y),
    D.compose (eta Y) (F.fmap f) = D.compose (G.fmap f) (eta X).
End NaturalTransformation.

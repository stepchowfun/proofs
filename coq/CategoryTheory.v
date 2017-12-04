(******************************************************)
(******************************************************)
(****                                              ****)
(****   A formalization of some category theory.   ****)
(****                                              ****)
(******************************************************)
(******************************************************)

(**************)
(* Categories *)
(**************)

Module Type Category.
  Parameter Object : Set.
  Parameter Arrow : Object -> Object -> Set.
  Parameter compose : forall {X Y Z}, Arrow Y Z -> Arrow X Y -> Arrow X Z.
  Parameter id : forall {X}, Arrow X X.

  Axiom assoc :
    forall W X Y Z (f : Arrow W X) (g : Arrow X Y) (h : Arrow Y Z),
    compose h (compose g f) = compose (compose h g) f.
  Axiom ident :
    forall X Y,
    (forall (f : Arrow X Y), compose f id = f) /\
    (forall (f : Arrow Y X), compose id f = f).
End Category.

(************)
(* Functors *)
(************)

Module Type Functor (C D : Category).
  Parameter omap : C.Object -> D.Object.
  Parameter fmap : forall {X Y}, C.Arrow X Y -> D.Arrow (omap X) (omap Y).

  Axiom ident : forall X, fmap (@C.id X) = @D.id (omap X).
  Axiom comp :
    forall X Y Z (f : C.Arrow X Y) (g : C.Arrow Y Z),
    fmap (C.compose g f) = D.compose (fmap g) (fmap f).
End Functor.

Module IdentityFunctor (C : Category) : Functor C C.
  Definition omap (X : C.Object) := X.
  Definition fmap {X Y} (f : C.Arrow X Y) := f.

  Theorem ident : forall X, fmap (@C.id X) = @C.id (omap X).
  Proof.
    auto.
  Qed.

  Theorem comp :
    forall X Y Z (f : C.Arrow X Y) (g : C.Arrow Y Z),
    fmap (C.compose g f) = C.compose (fmap g) (fmap f).
  Proof.
    auto.
  Qed.
End IdentityFunctor.

Module CompositeFunctor
    (C D E : Category)
    (F : Functor D E)
    (G : Functor C D) :
    Functor C E.
  Definition omap (X : C.Object) := F.omap (G.omap X).
  Definition fmap {X Y} (f : C.Arrow X Y) := F.fmap (G.fmap f).

  Theorem ident : forall X, fmap (@C.id X) = @E.id (omap X).
  Proof.
    intros.
    unfold fmap.
    replace (G.fmap C.id) with (@D.id (G.omap X)).
    - apply F.ident.
    - symmetry; apply G.ident.
  Qed.

  Theorem comp :
    forall X Y Z (f : C.Arrow X Y) (g : C.Arrow Y Z),
    fmap (C.compose g f) = E.compose (fmap g) (fmap f).
  Proof.
    intros.
    unfold fmap.
    replace (G.fmap (C.compose g f)) with (D.compose (G.fmap g) (G.fmap f)).
    - apply F.comp.
    - symmetry; apply G.comp.
  Qed.
End CompositeFunctor.

(***************************)
(* Natural transformations *)
(***************************)

Module Type NaturalTransformation (C D : Category) (F G : Functor C D).
  Parameter eta : forall X, D.Arrow (F.omap X) (G.omap X).

  Axiom commute :
    forall X Y (f : C.Arrow X Y),
    D.compose (eta Y) (F.fmap f) = D.compose (G.fmap f) (eta X).
End NaturalTransformation.

Module IdentityNaturalTransformation
    (C D : Category)
    (F : Functor C D) :
    NaturalTransformation C D F F.
  Definition eta X := @D.id (F.omap X).

  Theorem commute :
    forall X Y (f : C.Arrow X Y),
    D.compose (eta Y) (F.fmap f) = D.compose (F.fmap f) (eta X).
  Proof.
    intros.
    unfold eta.
    replace (D.compose D.id (F.fmap f)) with (F.fmap f);
      symmetry;
      apply D.ident.
  Qed.
End IdentityNaturalTransformation.

Module VerticalCompositeNaturalTransformation
    (C D : Category)
    (F G H : Functor C D)
    (Eta : NaturalTransformation C D G H)
    (Mu : NaturalTransformation C D F G) :
    NaturalTransformation C D F H.
  Definition eta X := D.compose (Eta.eta X) (Mu.eta X).

  Theorem commute :
    forall X Y (f : C.Arrow X Y),
    D.compose (eta Y) (F.fmap f) = D.compose (H.fmap f) (eta X).
  Proof.
    intros.
    unfold eta.
    replace (D.compose (D.compose (Eta.eta Y) (Mu.eta Y)) (F.fmap f)) with
      (D.compose (Eta.eta Y) (D.compose (Mu.eta Y) (F.fmap f))).
    - replace (D.compose (H.fmap f) (D.compose (Eta.eta X) (Mu.eta X))) with
      (D.compose (D.compose (H.fmap f) (Eta.eta X)) (Mu.eta X)).
      + replace (D.compose (Mu.eta Y) (F.fmap f)) with
        (D.compose (G.fmap f) (Mu.eta X)).
        * {
          replace (D.compose (H.fmap f) (Eta.eta X)) with
            (D.compose (Eta.eta Y) (G.fmap f)).
          - apply D.assoc.
          - apply Eta.commute.
        }
        * symmetry; apply Mu.commute.
      + symmetry; apply D.assoc.
    - apply D.assoc.
  Qed.
End VerticalCompositeNaturalTransformation.

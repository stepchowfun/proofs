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
  Parameter Object : Type.
  Parameter Arrow : Object -> Object -> Type.
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

(*************************)
(* Example category: Set *)
(*************************)

Module SetCategory : Category.
  Definition Object := Set.
  Definition Arrow (X : Object) (Y : Object) := forall (_ : X), Y.
  Definition compose {X Y Z} (f : Arrow Y Z) (g : Arrow X Y) x := f (g x).
  Definition id {X : Object} := fun (x : X) => x.

  Theorem assoc :
    forall W X Y Z (f : Arrow W X) (g : Arrow X Y) (h : Arrow Y Z),
    compose h (compose g f) = compose (compose h g) f.
  Proof.
    auto.
  Qed.

  Theorem ident :
    forall X Y,
    (forall (f : Arrow X Y), compose f id = f) /\
    (forall (f : Arrow Y X), compose id f = f).
  Proof.
    auto.
  Qed.
End SetCategory.

(************)
(* Functors *)
(************)

Module Type Functor (C D : Category).
  Parameter oMap : C.Object -> D.Object.
  Parameter fMap : forall {X Y}, C.Arrow X Y -> D.Arrow (oMap X) (oMap Y).

  Axiom ident : forall X, fMap (@C.id X) = @D.id (oMap X).
  Axiom comp :
    forall X Y Z (f : C.Arrow X Y) (g : C.Arrow Y Z),
    fMap (C.compose g f) = D.compose (fMap g) (fMap f).
End Functor.

Module IdentityFunctor (C : Category) : Functor C C.
  Definition oMap (X : C.Object) := X.
  Definition fMap {X Y} (f : C.Arrow X Y) := f.

  Theorem ident : forall X, fMap (@C.id X) = @C.id (oMap X).
  Proof.
    auto.
  Qed.

  Theorem comp :
    forall X Y Z (f : C.Arrow X Y) (g : C.Arrow Y Z),
    fMap (C.compose g f) = C.compose (fMap g) (fMap f).
  Proof.
    auto.
  Qed.
End IdentityFunctor.

Module FunctorComposition
    (C D E : Category)
    (F : Functor D E)
    (G : Functor C D) :
    Functor C E.
  Definition oMap (X : C.Object) := F.oMap (G.oMap X).
  Definition fMap {X Y} (f : C.Arrow X Y) := F.fMap (G.fMap f).

  Theorem ident : forall X, fMap (@C.id X) = @E.id (oMap X).
  Proof.
    intros.
    unfold fMap.
    replace (G.fMap C.id) with (@D.id (G.oMap X)).
    - apply F.ident.
    - symmetry; apply G.ident.
  Qed.

  Theorem comp :
    forall X Y Z (f : C.Arrow X Y) (g : C.Arrow Y Z),
    fMap (C.compose g f) = E.compose (fMap g) (fMap f).
  Proof.
    intros.
    unfold fMap.
    replace (G.fMap (C.compose g f)) with (D.compose (G.fMap g) (G.fMap f)).
    - apply F.comp.
    - symmetry; apply G.comp.
  Qed.
End FunctorComposition.

(***************************)
(* Natural transformations *)
(***************************)

Module Type NaturalTransformation (C D : Category) (F G : Functor C D).
  Parameter eta : forall X, D.Arrow (F.oMap X) (G.oMap X).

  Axiom naturality :
    forall X Y (f : C.Arrow X Y),
    D.compose (eta Y) (F.fMap f) = D.compose (G.fMap f) (eta X).
End NaturalTransformation.

Module IdentityNaturalTransformation
    (C D : Category)
    (F : Functor C D) :
    NaturalTransformation C D F F.
  Definition eta X := @D.id (F.oMap X).

  Theorem naturality :
    forall X Y (f : C.Arrow X Y),
    D.compose (eta Y) (F.fMap f) = D.compose (F.fMap f) (eta X).
  Proof.
    intros.
    unfold eta.
    replace (D.compose D.id (F.fMap f)) with (F.fMap f);
      symmetry;
      apply D.ident.
  Qed.
End IdentityNaturalTransformation.

Module VerticalComposition
    (C D : Category)
    (F G H : Functor C D)
    (Eta : NaturalTransformation C D G H)
    (Mu : NaturalTransformation C D F G) :
    NaturalTransformation C D F H.
  Definition eta X := D.compose (Eta.eta X) (Mu.eta X).

  Theorem naturality :
    forall X Y (f : C.Arrow X Y),
    D.compose (eta Y) (F.fMap f) = D.compose (H.fMap f) (eta X).
  Proof.
    intros.
    unfold eta.
    replace (D.compose (D.compose (Eta.eta Y) (Mu.eta Y)) (F.fMap f)) with
      (D.compose (Eta.eta Y) (D.compose (Mu.eta Y) (F.fMap f))).
    - replace (D.compose (H.fMap f) (D.compose (Eta.eta X) (Mu.eta X))) with
      (D.compose (D.compose (H.fMap f) (Eta.eta X)) (Mu.eta X)).
      + replace (D.compose (Mu.eta Y) (F.fMap f)) with
        (D.compose (G.fMap f) (Mu.eta X)).
        * {
          replace (D.compose (H.fMap f) (Eta.eta X)) with
            (D.compose (Eta.eta Y) (G.fMap f)).
          - apply D.assoc.
          - apply Eta.naturality.
        }
        * symmetry; apply Mu.naturality.
      + symmetry; apply D.assoc.
    - apply D.assoc.
  Qed.
End VerticalComposition.

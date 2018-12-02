(**********************)
(**********************)
(****              ****)
(****   Functors   ****)
(****              ****)
(**********************)
(**********************)

Require Import Main.CategoryTheory.Category.
Require Import Main.Tactics.

Set Universe Polymorphism.

(* Metavariables for functors: F, G, H *)

Record functor {C D : category} := newFunctor {
  oMap : object C -> object D;
  fMap {x y} : arrow C x y -> arrow D (oMap x) (oMap y);

  fIdent x : fMap (@id C x) = @id D (oMap x);
  fComp x y z (f : arrow C x y) (g : arrow C y z) :
    compose D (fMap g) (fMap f) = fMap (compose C g f);
}.

Hint Resolve @fIdent.
Hint Rewrite @fIdent.
Hint Resolve @fComp.
Hint Rewrite @fComp.

Let idFIdent {C : category} (x : object C) : @id C x = @id C x.
Proof.
  magic.
Qed.

Let idFComp
  {C : category}
  (x y z : object C)
  (f : arrow C x y)
  (g : arrow C y z)
: compose C g f = compose C g f.
Proof.
  magic.
Qed.

Definition idFunctor {C : category} : @functor C C := newFunctor C C
  (fun x => x)
  (fun x y f => f)
  idFIdent
  idFComp.

Let compFIdent
  {C D E : category}
  {G : @functor D E}
  {F : @functor C D}
  (x : object C)
: fMap G (fMap F (@id C x)) = id E.
Proof.
  magic.
Qed.

Let compFComp
  {C D E : category}
  {G : @functor D E}
  {F : @functor C D}
  (x y z : object C)
  (f : arrow C x y)
  (g : arrow C y z)
: compose E (fMap G (fMap F g)) (fMap G (fMap F f)) =
  fMap G (fMap F (compose C g f)).
Proof.
  magic.
Qed.

Definition compFunctor
  {C D E : category}
  (G : @functor D E)
  (F : @functor C D) :
  @functor C E
:= newFunctor C E
  (fun (x : object C) => oMap G (oMap F x))
  (fun {x y : object C} (f : arrow C x y) => fMap G (fMap F f))
  compFIdent
  compFComp.

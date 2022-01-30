(**********************)
(**********************)
(****              ****)
(****   Functors   ****)
(****              ****)
(**********************)
(**********************)

Require Import Main.CategoryTheory.Category.
Require Import Main.Tactics.
Require Import ProofIrrelevance.

Set Universe Polymorphism.

(* Metavariables for functors: F, G, H *)

Record functor C D := newFunctor {
  oMap : object C -> object D;
  fMap {x y} : arrow x y -> arrow (oMap x) (oMap y);

  fIdent x : fMap (@id C x) = @id D (oMap x);
  fComp {x y z} (f : arrow x y) (g : arrow y z) :
    compose (fMap g) (fMap f) = fMap (compose g f);
}.

Arguments oMap {_} {_} _.
Arguments fMap {_} {_} _ {_} {_}.
Arguments fIdent {_} {_} _.
Arguments fComp {_} {_} _ {_} {_} {_}.

#[export] Hint Resolve fIdent : core.
#[export] Hint Rewrite @fIdent : core.
#[export] Hint Resolve fComp : core.
#[export] Hint Rewrite @fComp : core.

Definition endofunctor C := functor C C.

Local Theorem compFIdent
  {C D E}
  {G : functor D E}
  {F : functor C D}
  (x : object C)
: fMap G (fMap F (@id C x)) = id.
Proof.
  magic.
Qed.

Local Theorem compFComp
  {C D E}
  {G : functor D E}
  {F : functor C D}
  (x y z : object C)
  (f : arrow x y)
  (g : arrow y z)
: compose (fMap G (fMap F g)) (fMap G (fMap F f)) =
  fMap G (fMap F (compose g f)).
Proof.
  magic.
Qed.

Definition compFunctor
  {C D E}
  (G : functor D E)
  (F : functor C D) :
  functor C E
:= newFunctor C E
  (fun x => oMap G (oMap F x))
  (fun x y (f : arrow x y) => fMap G (fMap F f))
  compFIdent
  compFComp.

Local Theorem idFIdent {C} (x : object C) : @id C x = id.
Proof.
  magic.
Qed.

Local Theorem idFComp {C} (x y z : object C) (f : arrow x y) (g : arrow y z) :
  compose g f = compose g f.
Proof.
  magic.
Qed.

Definition idFunctor {C} : functor C C := newFunctor C C
  (fun x => x)
  (fun _ _ f => f)
  idFIdent
  idFComp.

Theorem compFunctorAssoc
  {B C D E}
  (F : functor B C)
  (G : functor C D)
  (H : functor D E)
: compFunctor H (compFunctor G F) = compFunctor (compFunctor H G) F.
Proof.
  unfold compFunctor.
  f_equal; apply proof_irrelevance.
Qed.

Theorem compFunctorIdentLeft {C D} (F : functor C D) :
  compFunctor idFunctor F = F.
Proof.
  unfold compFunctor.
  destruct F.
  f_equal; apply proof_irrelevance.
Qed.

Theorem compFunctorIdentRight {C D} (F : functor C D) :
  compFunctor F idFunctor = F.
Proof.
  unfold compFunctor.
  destruct F.
  f_equal; apply proof_irrelevance.
Qed.

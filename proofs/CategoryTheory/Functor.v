(**********************)
(**********************)
(****              ****)
(****   Functors   ****)
(****              ****)
(**********************)
(**********************)

Require Import Coq.Logic.ProofIrrelevance.
Require Import Main.CategoryTheory.Category.
Require Import Main.Tactics.

#[local] Obligation Tactic := search.
#[local] Set Universe Polymorphism.

(* Metavariables for functors: `F`, `G`, `H` *)

Record functor C D := {
  oMap : object C -> object D;
  fMap [x y] : arrow x y -> arrow (oMap x) (oMap y);

  fIdent x : fMap (id x) = id (oMap x);
  fComp [x y z] (f : arrow x y) (g : arrow y z) :
    compose (fMap f) (fMap g) = fMap (compose f g);
}.

Arguments oMap [_ _] _.
Arguments fMap [_ _] _ [_ _] _.
Arguments fIdent [_ _] _ _.
Arguments fComp [_ _] _ [_ _ _] _ _.

#[export] Hint Resolve fIdent : main.
#[export] Hint Rewrite @fIdent : main.
#[export] Hint Resolve fComp : main.
#[export] Hint Rewrite @fComp : main.

Definition endofunctor C := functor C C.

Program Definition idFunctor C : endofunctor C := {|
  oMap o := o;
  fMap _ _ f := f;
|}.

Program Definition compFunctor [C D E] (F : functor C D) (G : functor D E) :
  functor C E
:= {|
  oMap o := oMap G (oMap F o);
  fMap _ _ f := fMap G (fMap F f);
|}.

Theorem compFunctorIdentLeft [C D] (F : functor C D) :
  compFunctor (idFunctor C) F = F.
Proof.
  unfold compFunctor.
  destruct F.
  f_equal; apply proof_irrelevance.
Qed.

#[export] Hint Resolve compFunctorIdentLeft : main.

Theorem compFunctorIdentRight [C D] (F : functor C D) :
  compFunctor F (idFunctor D) = F.
Proof.
  unfold compFunctor.
  destruct F.
  f_equal; apply proof_irrelevance.
Qed.

#[export] Hint Resolve compFunctorIdentRight : main.

Theorem compFunctorAssoc
  [B C D E]
  (F : functor B C)
  (G : functor C D)
  (H : functor D E)
: compFunctor (compFunctor F G) H = compFunctor F (compFunctor G H).
Proof.
  unfold compFunctor.
  f_equal; apply proof_irrelevance.
Qed.

#[export] Hint Resolve compFunctorAssoc : main.

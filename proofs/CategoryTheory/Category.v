(************************)
(************************)
(****                ****)
(****   Categories   ****)
(****                ****)
(************************)
(************************)

Require Import Coq.Logic.ProofIrrelevance.
Require Import Main.Tactics.

#[local] Obligation Tactic := search.
#[local] Set Universe Polymorphism.

(* Metavariables for categories: `C`, `D`, `E` *)

Record isCategory
  (object : Type) (* Objects: `w`, `x`, `y`, `z` *)
  (arrow : object -> object -> Type) (* Arrows: `f`, `g`, `h` *)
  (id : forall x, arrow x x)
  (compose : forall {x y z}, arrow x y -> arrow y z -> arrow x z)
:= {
  isCIdentLeft x y (f : arrow x y) : compose (id x) f = f;
  isCIdentRight x y (f : arrow x y) : compose f (id y) = f;
  isCAssoc w x y z (f : arrow w x) (g : arrow x y) (h : arrow y z) :
    compose (compose f g) h = compose f (compose g h);
}.

Arguments isCIdentLeft {_ _ _ _ _ _ _} _.
Arguments isCIdentRight {_ _ _ _ _ _ _} _.
Arguments isCAssoc {_ _ _ _ _ _ _ _ _} _ _ _.

#[export] Hint Constructors isCategory : main.

Record category := {
  object; arrow; id; compose;
  categoryLaws : isCategory object arrow id compose;
}.

Arguments arrow {_} _ _.
Arguments id {_} _.
Arguments compose {_ _ _ _} _ _.

Definition cIdentLeft {C : category} {x y : object C} (f : arrow x y) :
  compose (id x) f = f
:= C.(categoryLaws).(isCIdentLeft) f.

Definition cIdentRight {C : category} {x y : object C} (f : arrow x y) :
  compose f (id y) = f
:= C.(categoryLaws).(isCIdentRight) f.

Definition cAssoc
  {C : category}
  {w x y z : object C}
  (f : arrow w x)
  (g : arrow x y)
  (h : arrow y z) :
  compose (compose f g) h = compose f (compose g h)
:= C.(categoryLaws).(isCAssoc) f g h.

#[export] Hint Resolve cAssoc : main.
#[export] Hint Resolve cIdentLeft : main.
#[export] Hint Rewrite @cIdentLeft : main.
#[export] Hint Resolve cIdentRight : main.
#[export] Hint Rewrite @cIdentRight : main.

Program Definition oppositeCategory C : category := {|
  object := object C;
  arrow f g := arrow g f;
  id x := id x;
  compose _ _ _ f g := compose g f;
|}.

Theorem oppositeInvolution C : oppositeCategory (oppositeCategory C) = C.
Proof.
  destruct C.
  unfold oppositeCategory.
  f_equal; apply proof_irrelevance.
Qed.

#[export] Hint Resolve oppositeInvolution : main.

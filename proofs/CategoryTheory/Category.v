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

Record category := {
  object : Type; (* Objects: `w`, `x`, `y`, `z` *)
  arrow : object -> object -> Type; (* Arrows: `f`, `g`, `h` *)
  id x : arrow x x;
  compose {x y z} : arrow x y -> arrow y z -> arrow x z;

  cIdentLeft {x y} (f : arrow x y) : compose (id x) f = f;
  cIdentRight {x y} (f : arrow x y) : compose f (id y) = f;
  cAssoc {w x y z} (f : arrow w x) (g : arrow x y) (h : arrow y z) :
    compose (compose f g) h = compose f (compose g h);
}.

Arguments arrow {_}.
Arguments id {_} _.
Arguments compose {_ _ _ _} _ _.
Arguments cIdentLeft {_ _ _} _.
Arguments cIdentRight {_ _ _} _.
Arguments cAssoc {_ _ _ _ _} _ _ _.

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

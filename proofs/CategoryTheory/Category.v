(************************)
(************************)
(****                ****)
(****   Categories   ****)
(****                ****)
(************************)
(************************)

Require Import Main.Tactics.
Require Import ProofIrrelevance.

Set Universe Polymorphism.

(* Metavariables for categories: C, D, E *)

Record category := newCategory {
  object : Type; (* Metavariables for objects: w, x, y, z *)
  arrow : object -> object -> Type; (* Metavariables for arrows: f, g, h *)
  compose {x y z} : arrow y z -> arrow x y -> arrow x z;
  id {x}: arrow x x;

  cAssoc {w x y z} (f : arrow w x) (g : arrow x y) (h : arrow y z) :
    compose h (compose g f) = compose (compose h g) f;
  cIdentLeft {x y} (f : arrow x y) : compose id f = f;
  cIdentRight {x y} (f : arrow x y) : compose f id = f;
}.

Arguments arrow {_}.
Arguments compose {_} {_} {_} {_}.
Arguments id {_} {_}.
Arguments cAssoc {_} {_} {_} {_} {_}.
Arguments cIdentLeft {_} {_} {_}.
Arguments cIdentRight {_} {_} {_}.

#[export] Hint Resolve cAssoc : main.
#[export] Hint Resolve cIdentLeft : main.
#[export] Hint Rewrite @cIdentLeft : main.
#[export] Hint Resolve cIdentRight : main.
#[export] Hint Rewrite @cIdentRight : main.

#[local] Theorem opCAssoc
  {C}
  (w x y z : object C)
  (f : arrow x w)
  (g : arrow y x)
  (h : arrow z y)
: compose (compose f g) h = compose f (compose g h).
Proof.
  magic.
Qed.

#[local] Theorem opCIdentLeft {C} (x y : object C) (f : arrow y x) :
  compose f id = f.
Proof.
  magic.
Qed.

#[local] Theorem opCIdentRight {C} (x y : object C) (f : arrow y x) :
  compose id f = f.
Proof.
  magic.
Qed.

Definition oppositeCategory C : category := newCategory
  (object C)
  (fun x y => arrow y x)
  (fun _ _ _ f g => compose g f)
  (fun _ => id)
  opCAssoc
  opCIdentLeft
  opCIdentRight.

Theorem oppositeInvolution C : oppositeCategory (oppositeCategory C) = C.
Proof.
  unfold oppositeCategory.
  destruct C.
  f_equal; apply proof_irrelevance.
Qed.

#[export] Hint Resolve oppositeInvolution : main.

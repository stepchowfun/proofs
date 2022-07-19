(*****************************************************)
(*****************************************************)
(****                                             ****)
(****   A formalization of the univalence axiom   ****)
(****                                             ****)
(*****************************************************)
(*****************************************************)

Definition equivalence {X Y : Set} (f : X -> Y) :=
  forall y,
  let fiber := { x | f x = y }
  in { x : fiber | forall z : fiber, x = z }.

Definition equalityToEquivalence (X Y : Set) (H : X = Y) :
  { f : X -> Y & equivalence f }.
Proof.
  rewrite <- H.
  exists (@id X).
  unfold equivalence.
  intros.
  exists (exist (fun x => x = y) y eq_refl).
  intros.
  destruct z.
  rewrite <- e.
  reflexivity.
Defined.

Axiom univalence : forall X Y, equivalence (equalityToEquivalence X Y).

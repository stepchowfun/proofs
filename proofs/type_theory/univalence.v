(*****************************************************)
(*****************************************************)
(****                                             ****)
(****   A formalization of the univalence axiom   ****)
(****                                             ****)
(*****************************************************)
(*****************************************************)

Definition Equivalence [X Y : Set] (f : X -> Y) : Set :=
  forall y,
  let fiber := { x | f x = y }
  in { x : fiber | forall z : fiber, x = z }.

Definition equality_to_equivalence (X Y : Set) (H : X = Y) :
  { f : X -> Y & Equivalence f }.
Proof.
  rewrite <- H.
  exists (@id X).
  unfold Equivalence.
  intros.
  exists (exist (fun x => x = y) y eq_refl).
  intros.
  destruct z.
  rewrite <- e.
  reflexivity.
Defined.

Axiom univalence : forall X Y, Equivalence (equality_to_equivalence X Y).

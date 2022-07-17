(*****************************************************)
(*****************************************************)
(****                                             ****)
(****   A formalization of the univalence axiom   ****)
(****                                             ****)
(*****************************************************)
(*****************************************************)

Definition contractible (X : Set) := exists x : X, forall y : X, x = y.

Definition equivalence {X Y : Set} (f : X -> Y) :=
  forall y, contractible { x | f x = y }.

Definition equalityToEquivalence (X Y : Set) (H : X = Y) :
  { f : X -> Y | equivalence f }.
Proof.
  rewrite H.
  exists (@id Y).
  unfold equivalence.
  intros.
  exists (exist (fun x => x = y) y eq_refl).
  intros.
  destruct y0.
  rewrite <- e.
  reflexivity.
Qed.

Axiom univalence : forall X Y, equivalence (equalityToEquivalence X Y).

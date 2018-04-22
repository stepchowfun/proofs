(*******************************************)
(*******************************************)
(****                                   ****)
(****   Names with decidable equality   ****)
(****                                   ****)
(*******************************************)
(*******************************************)

Require Import List.
Require Import Main.Tactics.

Module Type NameSig.

  Parameter name : Set.

  Axiom nameEq : forall x1 x2 : name, { x1 = x2 } + { x1 <> x2 }.

  Axiom nameFresh : forall l : list name, exists x, ~ In x l.

End NameSig.

Module Name : NameSig.

  Definition name := nat.

  Theorem nameEq : forall x1 x2 : nat, { x1 = x2 } + { x1 <> x2 }.
  Proof.
    induction x1; magic.
  Qed.

  Hint Resolve nameEq.

  Theorem nameFresh : forall l : list nat, exists x, ~ In x l.
  Proof.
    clean. exists (S (fold_right max 0 l)). unfold not. clean.
    assert (forall n, In n l -> n < S (fold_right Nat.max 0 l)).
    - clear H. clean. induction l; magic.
      assert ((fold_right max 0 l) < S (max a (fold_right max 0 l))); magic.
    - specialize (H0 (S (fold_right Nat.max 0 l))). magic.
  Qed.

  Hint Resolve nameFresh.

End Name.

Export Name.

(************************************)
(* Miscellaneous facts about names. *)
(************************************)

Theorem nameInRemove :
  forall l x1 x2,
  In x1 (remove nameEq x2 l) ->
  In x1 l /\ x1 <> x2.
Proof.
  clean. induction l; magic.
Qed.

Hint Resolve nameInRemove.

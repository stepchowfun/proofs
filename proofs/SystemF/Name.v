(*******************************************)
(*******************************************)
(****                                   ****)
(****   Names with decidable equality   ****)
(****                                   ****)
(*******************************************)
(*******************************************)

Require Import Coq.Arith.Peano_dec.
Require Import Coq.Lists.List.
Require Import Main.Tactics.

Module Type NameSig.

  Parameter name : Type.

  Axiom nameEq : forall x1 x2 : name, { x1 = x2 } + { x1 <> x2 }.

  Axiom nameFresh : forall l : list name, exists x, ~ In x l.

End NameSig.

Module Name : NameSig.

  Definition name := nat.

  Theorem nameEq : forall x1 x2 : nat, { x1 = x2 } + { x1 <> x2 }.
  Proof.
    induction x1; search.
  Qed.

  #[export] Hint Resolve nameEq : main.

  Theorem nameFresh : forall l : list nat, exists x, ~ In x l.
  Proof.
    clean. exists (S (fold_right max 0 l)). unfold not. clean.
    assert (forall n, In n l -> n < S (fold_right Nat.max 0 l)).
    - clear H. clean. induction l; search.
      assert ((fold_right max 0 l) < S (max a (fold_right max 0 l))); search.
      destruct H; search.
    - specialize (H0 (S (fold_right Nat.max 0 l))). search.
  Qed.

  #[export] Hint Resolve nameFresh : main.

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
  clean. induction l; search.
Qed.

#[export] Hint Resolve nameInRemove : main.

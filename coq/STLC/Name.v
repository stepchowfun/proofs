(*******************************************)
(*******************************************)
(****                                   ****)
(****   Names with decidable equality   ****)
(****                                   ****)
(*******************************************)
(*******************************************)

Require Import Main.Tactics.

Module Type NameSig.

  Parameter name : Set.

  Axiom nameEq : forall x1 x2 : name, { x1 = x2 } + { x1 <> x2 }.

End NameSig.

Module Name : NameSig.

  Definition name := nat.

  Theorem nameEq : forall x1 x2 : nat, { x1 = x2 } + { x1 <> x2 }.
  Proof.
    intro.
    induction x1; intro; destruct x2; magic.
    specialize (IHx1 x2).
    magic.
  Qed.

  Hint Resolve nameEq.

End Name.

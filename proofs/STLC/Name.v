(*******************************************)
(*******************************************)
(****                                   ****)
(****   Names with decidable equality   ****)
(****                                   ****)
(*******************************************)
(*******************************************)

Require Import Coq.Arith.Peano_dec.
Require Import Main.Tactics.

Module Type NameSig.

  Parameter name : Type.

  Axiom nameEq : forall x1 x2 : name, { x1 = x2 } + { x1 <> x2 }.

End NameSig.

Module Name : NameSig.

  Definition name := nat.

  Theorem nameEq : forall x1 x2 : nat, { x1 = x2 } + { x1 <> x2 }.
  Proof.
    induction x1; search.
  Qed.

  #[export] Hint Resolve nameEq : main.

End Name.

Export Name.

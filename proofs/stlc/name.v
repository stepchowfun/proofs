(*******************************************)
(*******************************************)
(****                                   ****)
(****   Names with decidable equality   ****)
(****                                   ****)
(*******************************************)
(*******************************************)

Require Import Stdlib.Arith.Peano_dec.
Require Import main.tactics.

Module Type NameSig.

  Parameter Name : Type.

  Axiom name_eq : forall x1 x2 : Name, { x1 = x2 } + { x1 <> x2 }.

End NameSig.

Module Name : NameSig.

  Definition Name := nat.

  Theorem name_eq : forall x1 x2 : nat, { x1 = x2 } + { x1 <> x2 }.
  Proof.
    induction x1; search.
  Qed.

  Hint Resolve name_eq : main.

End Name.

Export Name.

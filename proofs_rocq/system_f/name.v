(*******************************************)
(*******************************************)
(****                                   ****)
(****   Names with decidable equality   ****)
(****                                   ****)
(*******************************************)
(*******************************************)

Require Import Stdlib.Arith.Peano_dec.
Require Import Stdlib.Lists.List.
Require Import main.tactics.

Module Type NameSig.

  Parameter Name : Type.

  Axiom name_eq : forall x1 x2 : Name, { x1 = x2 } + { x1 <> x2 }.

  Axiom name_fresh : forall l : list Name, exists x, ~ In x l.

End NameSig.

Module Name : NameSig.

  Definition Name := nat.

  Theorem name_eq : forall x1 x2 : nat, { x1 = x2 } + { x1 <> x2 }.
  Proof.
    induction x1; search.
  Qed.

  Hint Resolve name_eq : main.

  Theorem name_fresh : forall l : list nat, exists x, ~ In x l.
  Proof.
    clean. exists (S (fold_right max 0 l)). unfold not. clean.
    assert (forall n, In n l -> n < S (fold_right Nat.max 0 l)).
    - clear H. clean. induction l; search.
      assert ((fold_right max 0 l) < S (max a (fold_right max 0 l))); search.
      destruct H; search.
    - specialize (H0 (S (fold_right Nat.max 0 l))). search.
  Qed.

  Hint Resolve name_fresh : main.

End Name.

Export Name.

(************************************)
(* Miscellaneous facts about names. *)
(************************************)

Theorem name_in_remove :
  forall l x1 x2,
  In x1 (remove name_eq x2 l) ->
  In x1 l /\ x1 <> x2.
Proof.
  clean. induction l; search.
Qed.

Hint Resolve name_in_remove : main.

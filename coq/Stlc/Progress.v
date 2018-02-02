(***********************************************************************)
(***********************************************************************)
(****                                                               ****)
(****   The progress theorem for the simply-typed lambda calculus   ****)
(****                                                               ****)
(***********************************************************************)
(***********************************************************************)

Require Import Main.Stlc.Semantics.
Require Import Main.Stlc.Syntax.
Require Import Main.Stlc.Typing.
Require Import Main.Tactics.

Theorem progress :
  forall e1 t,
  hasType cEmpty e1 t ->
  value e1 \/ exists e2, step e1 e2.
Proof.
  intros; remember cEmpty; induction H; magic.
  - right; destruct IHhasType1; magic.
    + destruct H2.
      * exists e2; magic.
      * exists e3; magic.
      * inversion H.
    + destruct H2; exists (eIf x e2 e3); magic.
  - subst c; inversion H.
  - right; destruct IHhasType1; destruct IHhasType2; magic.
    + inversion H2; inversion H0; magic; exists (sub e x e1); magic.
    + destruct H2; exists (eApp x e1); magic.
    + destruct H1; exists (eApp e2 x); magic.
    + destruct H2; exists (eApp x e1); magic.
Qed.

Hint Resolve progress.

(**************************************************************************)
(**************************************************************************)
(****                                                                  ****)
(****   Facts about the interaction between opening and substitution   ****)
(****                                                                  ****)
(**************************************************************************)
(**************************************************************************)

Require Import List.
Require Import Main.SystemF.FreeVar.
Require Import Main.SystemF.LocalClosure.
Require Import Main.SystemF.Name.
Require Import Main.SystemF.Opening.
Require Import Main.SystemF.Substitution.
Require Import Main.SystemF.Syntax.
Require Import Main.Tactics.

(*****************************)
(* Substitution introduction *)
(*****************************)

Theorem ttSubIntro :
  forall i t1 t2 x,
  ~ In x (tFreeVars t1) ->
  ttOpen t1 i t2 = (ttSub (ttOpen t1 i (tFreeVar x)) x t2).
Proof.
  clean. gen i. induction t1; magic.
Qed.

#[export] Hint Resolve ttSubIntro : core.

Theorem eeSubIntro :
  forall e1 e2 i x,
  ~ In x (eeFreeVars e1) ->
  eeOpen e1 i e2 = (eeSub (eeOpen e1 i (eFreeVar x)) x e2).
Proof.
  induction e1; magic.
Qed.

#[export] Hint Resolve eeSubIntro : core.

Theorem etSubIntro :
  forall e i t x,
  ~ In x (etFreeVars e) ->
  etOpen e i t = (etSub (etOpen e i (tFreeVar x)) x t).
Proof.
  induction e; magic; clean; rewrite ttSubIntro with (x := x); magic.
Qed.

#[export] Hint Resolve etSubIntro : core.

(******************************************)
(* Substitution distributes over opening. *)
(******************************************)

Theorem ttttSubOpen :
  forall i t1 t2 t3 x,
  tLocallyClosed t2 i ->
  ttSub (ttOpen t1 i t3) x t2 = ttOpen (ttSub t1 x t2) i (ttSub t3 x t2).
Proof.
  clean. gen i. induction t1; magic; clean.
  - destruct (nameEq x n); magic. rewrite tttOpenLocallyClosed; magic.
  - specialize (IHt1 (S i)). feed IHt1.
    apply tLocalClosureMonotonic with (i1 := i); magic.
Qed.

#[export] Hint Resolve ttttSubOpen : core.

Theorem eeeeSubOpen :
  forall e1 e2 e3 ie it x,
  eLocallyClosed e2 ie it ->
  eeSub (eeOpen e1 ie e3) x e2 = eeOpen (eeSub e1 x e2) ie (eeSub e3 x e2).
Proof.
  clean. gen ie. induction e1; magic; clean.
  - destruct (nameEq x n); magic.
    rewrite eeeOpenLocallyClosed with (it := it); magic.
  - specialize (IHe1 (S ie)). feed IHe1.
    apply eLocalClosureMonotonic with (ie1 := ie) (it1 := it); magic.
Qed.

#[export] Hint Resolve eeeeSubOpen : core.

Theorem eeetSubOpen :
  forall e1 e2 ie it t x,
  eLocallyClosed e2 ie it ->
  eeSub (etOpen e1 it t) x e2 = etOpen (eeSub e1 x e2) it t.
Proof.
  clean. gen it. induction e1; magic; clean.
  - destruct (nameEq x n); magic.
    rewrite eetOpenLocallyClosed with (ie := ie) (it := it); magic.
  - specialize (IHe1 (S it)). feed IHe1.
    apply eLocalClosureMonotonic with (ie1 := ie) (it1 := it); magic.
Qed.

#[export] Hint Resolve eeetSubOpen : core.

Theorem eteeSubOpen :
  forall i e1 e2 t x,
  tLocallyClosed t i ->
  etSub (eeOpen e1 i e2) x t = eeOpen (etSub e1 x t) i (etSub e2 x t).
Proof.
  clean. gen i. induction e1; magic; clean.
  specialize (IHe1 (S i)). feed IHe1.
  apply tLocalClosureMonotonic with (i1 := i); magic.
Qed.

#[export] Hint Resolve eteeSubOpen : core.

Theorem etetSubOpen :
  forall i e t1 t2 x,
  tLocallyClosed t1 i ->
  etSub (etOpen e i t2) x t1 = etOpen (etSub e x t1) i (ttSub t2 x t1).
Proof.
  clean. gen i. induction e; magic; clean.
  specialize (IHe (S i)). feed IHe.
  apply tLocalClosureMonotonic with (i1 := i); magic.
Qed.

#[export] Hint Resolve etetSubOpen : core.

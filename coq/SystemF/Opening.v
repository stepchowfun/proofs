(******************************)
(******************************)
(****                      ****)
(****   Variable opening   ****)
(****                      ****)
(******************************)
(******************************)

Require Import List.
Require Import Main.SystemF.FreeVar.
Require Import Main.SystemF.LocalClosure.
Require Import Main.SystemF.Syntax.
Require Import Main.Tactics.
Require Import Peano_dec.

Import PeanoNat.Nat.

Fixpoint eeOpen e1 i1 e2 :=
  match e1 with
  | eFreeVar _ => e1
  | eBoundVar i2 => if eq_nat_dec i1 i2 then e2 else e1
  | eAbs t e3 => eAbs t (eeOpen e3 (S i1) e2)
  | eApp e3 e4 => eApp (eeOpen e3 i1 e2) (eeOpen e4 i1 e2)
  | eTAbs e3 => eTAbs (eeOpen e3 i1 e2)
  | eTApp e3 t => eTApp (eeOpen e3 i1 e2) t
  end.

Fixpoint ttOpen t1 i1 t2 :=
  match t1 with
  | tFreeVar _ => t1
  | tBoundVar i2 => if eq_nat_dec i1 i2 then t2 else t1
  | tArrow t3 t4 => tArrow (ttOpen t3 i1 t2) (ttOpen t4 i1 t2)
  | tForAll t3 => tForAll (ttOpen t3 (S i1) t2)
  end.

Fixpoint etOpen e1 i1 t1 :=
  match e1 with
  | eFreeVar _ => e1
  | eBoundVar _ => e1
  | eAbs t2 e2 => eAbs (ttOpen t2 i1 t1) (etOpen e2 i1 t1)
  | eApp e2 e3 => eApp (etOpen e2 i1 t1) (etOpen e3 i1 t1)
  | eTAbs e2 => eTAbs (etOpen e2 (S i1) t1)
  | eTApp e2 t2 => eTApp (etOpen e2 i1 t1) (ttOpen t2 i1 t1)
  end.

(*****************************************************)
(* Opening a locally closed term/type has no effect. *)
(*****************************************************)

Theorem tttOpenLocallyClosed :
  forall i t1 t2,
  tLocallyClosed t1 i ->
  ttOpen t1 i t2 = t1.
Proof.
  clean. induction H; magic.
Qed.

Hint Resolve tttOpenLocallyClosed.

Theorem eeeOpenLocallyClosed :
  forall e1 e2 ie it,
  eLocallyClosed e1 ie it ->
  eeOpen e1 ie e2 = e1.
Proof.
  clean. induction H; magic.
Qed.

Hint Resolve eeeOpenLocallyClosed.

Theorem eetOpenLocallyClosed :
  forall e ie it t,
  eLocallyClosed e ie it ->
  etOpen e it t = e.
Proof.
  clean. induction H; magic.
Qed.

Hint Resolve eetOpenLocallyClosed.

(***************************************************************************)
(* If the opening of a term/type is locally closed at some level, then the *)
(* term/type is locally closed at the next level.                          *)
(***************************************************************************)

Theorem ttLocallyClosedOpen :
  forall i t1 t2,
  tLocallyClosed (ttOpen t1 i t2) i ->
  tLocallyClosed t1 (S i).
Proof.
  clean. gen t1 i.
  induction t1; magic; clean.
  - destruct (eq_dec i n); magic.
    apply tLocalClosureMonotonic with (i1 := i); magic.
  - invert H. magic.
  - invert H. magic.
Qed.

Hint Resolve ttLocallyClosedOpen.

Theorem eeLocallyClosedOpen :
  forall e1 e2 ie it,
  eLocallyClosed (eeOpen e1 ie e2) ie it ->
  eLocallyClosed e1 (S ie) it.
Proof.
  clean. gen e1 ie it.
  induction e1; magic; clean.
  - destruct (eq_dec ie n); magic.
    apply eLocalClosureMonotonic with (ie1 := ie) (it1 := it); magic.
  - invert H. magic.
  - invert H. magic.
  - invert H. magic.
  - invert H. magic.
Qed.

Hint Resolve eeLocallyClosedOpen.

Theorem etLocallyClosedOpen :
  forall e ie it t,
  eLocallyClosed (etOpen e it t) ie it ->
  eLocallyClosed e ie (S it).
Proof.
  clean. gen e ie it.
  induction e; magic; clean.
  - apply eLocalClosureMonotonic with (ie1 := ie) (it1 := it); magic.
  - invert H. eMagic.
  - invert H. magic.
  - invert H. magic.
  - invert H. eMagic.
Qed.

Hint Resolve etLocallyClosedOpen.

(********************************)
(* Free variables of an opening *)
(********************************)

Theorem tttFreeOpen :
  forall i t1 t2,
  incl (tFreeVars (ttOpen t1 i t2)) (tFreeVars t2 ++ tFreeVars t1) /\
  incl (tFreeVars t1) (tFreeVars (ttOpen t1 i t2)).
Proof.
  clean. split; gen i.
  - induction t1; magic. clean. apply incl_app.
    + apply incl_tran with (m := tFreeVars t2 ++ tFreeVars t1_1); magic.
    + apply incl_tran with (m := tFreeVars t2 ++ tFreeVars t1_2); magic.
  - induction t1; magic. unfold incl. magic.
Qed.

Hint Resolve tttFreeOpen.

Theorem eeeeFreeOpen :
  forall e1 e2 i,
  incl (eeFreeVars (eeOpen e1 i e2)) (eeFreeVars e2 ++ eeFreeVars e1) /\
  incl (eeFreeVars e1) (eeFreeVars (eeOpen e1 i e2)).
Proof.
  clean. split; gen i.
  - induction e1; magic. clean. apply incl_app.
    + apply incl_tran with (m := eeFreeVars e2 ++ eeFreeVars e1_1); magic.
    + apply incl_tran with (m := eeFreeVars e2 ++ eeFreeVars e1_2); magic.
  - induction e1; magic. unfold incl. magic.
Qed.

Hint Resolve eeeeFreeOpen.

Theorem eeetFreeOpen :
  forall e i t,
  incl (eeFreeVars (etOpen e i t)) (eeFreeVars e) /\
  incl (eeFreeVars e) (eeFreeVars (etOpen e i t)).
Proof.
  clean. split; gen i; induction e; magic.
Qed.

Hint Resolve eeetFreeOpen.

Theorem eteeFreeOpen :
  forall e1 e2 i,
  incl (etFreeVars (eeOpen e1 i e2)) (etFreeVars e2 ++ etFreeVars e1) /\
  incl (etFreeVars e1) (etFreeVars (eeOpen e1 i e2)).
Proof.
  clean. split; gen i.
  - induction e1; magic; clean.
    + specialize (IHe1 (S i)). apply incl_app; magic.
      apply incl_tran with (m := etFreeVars e2 ++ etFreeVars e1); magic.
    + specialize (IHe1_1 i). specialize (IHe1_2 i). apply incl_app; magic.
      * apply incl_tran with (m := etFreeVars e2 ++ etFreeVars e1_1); magic.
      * apply incl_tran with (m := etFreeVars e2 ++ etFreeVars e1_2); magic.
    + specialize (IHe1 i). apply incl_app; magic.
      apply incl_tran with (m := etFreeVars e2 ++ etFreeVars e1); magic.
  - induction e1; magic. unfold incl. magic.
Qed.

Hint Resolve eteeFreeOpen.

Theorem etetFreeOpen :
  forall e i t,
  incl (etFreeVars (etOpen e i t)) (tFreeVars t ++ etFreeVars e) /\
  incl (etFreeVars e) (etFreeVars (etOpen e i t)).
Proof.
  clean. split; gen i.
  - induction e; magic; clean; apply incl_app.
    + apply incl_tran with (m := tFreeVars t0 ++ tFreeVars t1); magic.
      apply tttFreeOpen.
    + apply incl_tran with (m := tFreeVars t0 ++ etFreeVars e); magic.
    + apply incl_tran with (m := tFreeVars t0 ++ etFreeVars e1); magic.
    + apply incl_tran with (m := tFreeVars t0 ++ etFreeVars e2); magic.
    + apply incl_tran with (m := tFreeVars t0 ++ etFreeVars e); magic.
    + apply incl_tran with (m := tFreeVars t0 ++ tFreeVars t1); magic.
      apply tttFreeOpen.
  - induction e; magic; clean;
      specialize (IHe i); apply incl_app; magic;
      apply incl_tran with (m := tFreeVars (ttOpen t1 i t0)); magic;
      apply tttFreeOpen.
Qed.

Hint Resolve etetFreeOpen.

(********************************************)
(* Opening binders preserves local closure. *)
(********************************************)

Theorem locallyClosedOpenForAll :
  forall i t1 t2,
  tLocallyClosed (tForAll t1) i ->
  tLocallyClosed t2 i ->
  tLocallyClosed (ttOpen t1 i t2) i.
Proof.
  clean. invert H.
  remember (S i). assert (n <= S i); magic. clear Heqn. gen t2 i.
  induction H2; magic; clean.
  constructor; magic.
  specialize (IHtLocallyClosed t2 (S i)).
  feed IHtLocallyClosed.
  apply tLocalClosureMonotonic with (i1 := i); magic.
Qed.

Hint Resolve locallyClosedOpenForAll.

Theorem locallyClosedOpenAbs :
  forall e1 e2 ie it t,
  eLocallyClosed (eAbs t e1) ie it ->
  eLocallyClosed e2 ie it ->
  eLocallyClosed (eeOpen e1 ie e2) ie it.
Proof.
  clean. invert H. clear t0 H3.
  remember (S ie). assert (n <= S ie); magic. clear Heqn. gen e2 ie.
  induction H6; magic; constructor; magic; clean; [
    specialize (IHeLocallyClosed e2 (S ie)) |
    specialize (IHeLocallyClosed e2 ie)
  ];
  feed IHeLocallyClosed;
  eapply eLocalClosureMonotonic with (ie1 := ie) (it1 := nt);
  magic.
Qed.

Hint Resolve locallyClosedOpenAbs.

Theorem locallyClosedOpenTAbs :
  forall e ie it t,
  eLocallyClosed (eTAbs e) ie it ->
  tLocallyClosed t it ->
  eLocallyClosed (etOpen e it t) ie it.
Proof.
  clean. invert H.
  remember (S it). assert (n <= S it); magic. clear Heqn. gen t it.
  induction H2; magic; constructor; magic; clean.
  - apply locallyClosedOpenForAll; magic.
    constructor.
    apply tLocalClosureMonotonic with (i1 := nt); magic.
  - specialize (IHeLocallyClosed t (S it)).
    feed IHeLocallyClosed.
    apply tLocalClosureMonotonic with (i1 := it); magic.
  - apply locallyClosedOpenForAll; magic.
    constructor.
    apply tLocalClosureMonotonic with (i1 := nt); magic.
Qed.

Hint Resolve locallyClosedOpenTAbs.

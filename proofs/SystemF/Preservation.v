(**************************************)
(**************************************)
(****                              ****)
(****   The preservation theorem   ****)
(****                              ****)
(**************************************)
(**************************************)

Require Import List.
Require Import Main.SystemF.Context.
Require Import Main.SystemF.FreeVar.
Require Import Main.SystemF.Name.
Require Import Main.SystemF.OpeningSubstitution.
Require Import Main.SystemF.Semantics.
Require Import Main.SystemF.Substitution.
Require Import Main.SystemF.Syntax.
Require Import Main.SystemF.Typing.
Require Import Main.Tactics.

Theorem eSubstitutionPreservesTyping :
  forall c1 c2 e1 e2 t1 t2 x,
  hasType (cConcat (cEExtend c1 x t2) c2) e1 t1 ->
  hasType c1 e2 t2 ->
  hasType (cConcat c1 c2) (eeSub e1 x e2) t1.
Proof.
  clean. remember (cConcat (cEExtend c1 x t2) c2). gen c2.
  induction H; eMagic; clean.
  - destruct (nameEq x x0); clean.
    + fact (cELookupNone (cEExtend c1 x0 t2) c2 t2 x0). clean.
      fact (cELookupConcatLeft (cEExtend c1 x0 t2) c2 t2 x0). clean.
      assert (t = t2); magic. clean. clear H3.
      replace (cConcat c1 c2) with (cConcat (cConcat c1 c2) cEmpty); magic.
      apply contextWeakening; magic. clean.
      apply cWellFormedESkip with (t := t2) (x := x0). magic.
    + constructor.
      * apply cWellFormedESkip with (t := t2) (x := x). magic.
      * clear H H0. induction c2; magic.
  - apply htAbs with (l := x :: l). clean.
    specialize (H1 x0). feed H1.
    replace (
      cEExtend (cConcat c1 c2) x0 t0
    ) with (
      cConcat c1 (cEExtend c2 x0 t0)
    ); magic.
    fact (typingRegularity c1 e2 t2).
    replace (eFreeVar x0) with (eeSub (eFreeVar x0) x e2); magic.
    rewrite <- eeeeSubOpen with (it := 0); magic.
  - apply htTAbs with (l := x :: l). clean.
    specialize (H1 x0). feed H1.
    replace (
      cTExtend (cConcat c1 c2) x0
    ) with (
      cConcat c1 (cTExtend c2 x0)
    ); magic.
    fact (typingRegularity c1 e2 t2).
    rewrite <- eeetSubOpen with (ie := 0); magic.
  - apply htTApp; magic.
    unfold tWellFormed in *. clean. split; magic.
    unfold incl in *. clean. specialize (H2 a). clean.
    rewrite tDomainConcat in *. clean. magic.
Qed.

#[export] Hint Resolve eSubstitutionPreservesTyping : core.

Theorem tSubstitutionPreservesTyping :
  forall c1 c2 e t1 t2 x,
  hasType (cConcat (cTExtend c1 x) c2) e t1 ->
  tWellFormed c1 t2 ->
  hasType (cConcat c1 (cSub c2 x t2)) (etSub e x t2) (ttSub t1 x t2).
Proof.
  clean. remember (cConcat (cTExtend c1 x) c2). gen c2.
  induction H; eMagic; clean.
  - constructor.
    + apply cWellFormedTSkip; magic.
    + clear H0. induction c2; invert H; magic; clean.
      rewrite tttSubBound; magic.
      fact (tWellFormedClosed c1 t x).
      feed H. apply tLookupWellFormed with (x := x0); magic.
  - apply htAbs with (l := x :: l). clean.
    specialize (H1 x0). feed H1.
    replace (
      cEExtend (cConcat c1 (cSub c2 x t2)) x0 (ttSub t0 x t2)
    ) with (
      cConcat c1 (cEExtend (cSub c2 x t2) x0 (ttSub t0 x t2))
    ); magic.
    unfold tWellFormed in H0.
    replace (eFreeVar x0) with (etSub (eFreeVar x0) x t2); magic.
    rewrite <- eteeSubOpen; magic.
    replace (
      cEExtend (cSub c2 x t2) x0 (ttSub t0 x t2)
    ) with (
      cSub (cEExtend c2 x0 t0) x t2
    ); magic.
  - apply htTAbs with (l := x :: l). clean.
    specialize (H1 x0). feed H1.
    replace (
      cTExtend (cConcat c1 (cSub c2 x t2)) x0
    ) with (
      cConcat c1 (cSub (cTExtend c2 x0) x t2)
    ); magic.
    unfold tWellFormed in H0.
    replace (tFreeVar x0) with (ttSub (tFreeVar x0) x t2); magic.
    rewrite <- etetSubOpen; magic.
    rewrite <- ttttSubOpen; magic.
  - unfold tWellFormed in H0.
    rewrite ttttSubOpen; magic.
    apply htTApp; magic.
    unfold tWellFormed in *. clean.
    split; magic.
    apply incl_tran with (
      m := tFreeVars t2 ++ remove nameEq x (tFreeVars t0)
    ); magic.
    unfold incl in *. clean.
    fact (in_app_or (tFreeVars t2) (remove nameEq x (tFreeVars t0)) a H4).
    clear H4. destruct H5; magic.
    rewrite tDomainConcat in *.
    fact (nameInRemove (tFreeVars t0) a x H4). clean. clear H4.
    specialize (H3 a). feed H3.
    rewrite cSubTDomain.
    fact (in_app_or (tDomain c2) (x :: tDomain c1) a H3).
    destruct H4; magic.
Qed.

#[export] Hint Resolve tSubstitutionPreservesTyping : core.

Theorem preservation :
  forall e1 e2 t,
  hasType cEmpty e1 t ->
  step e1 e2 ->
  hasType cEmpty e2 t.
Proof.
  clean. gen e2. remember cEmpty. induction H; magic; clean.
  - invert H; magic; invert H1; eMagic.
    fact (nameFresh (eeFreeVars e ++ l)). clean.
    specialize (H5 x). feed H5.
    rewrite eeSubIntro with (x := x); magic.
    replace cEmpty with (cConcat cEmpty cEmpty); eMagic.
  - invert H0; magic; invert H1; magic.
    fact (nameFresh (etFreeVars e0 ++ tFreeVars t1 ++ l)). clean.
    specialize (H5 x). feed H5.
    rewrite etSubIntro with (x := x); magic.
    rewrite ttSubIntro with (x := x); magic.
    replace cEmpty with (cConcat cEmpty (cSub cEmpty x t2)); eMagic.
Qed.

#[export] Hint Resolve preservation : core.

(**************************)
(**************************)
(****                  ****)
(****   Substitution   ****)
(****                  ****)
(**************************)
(**************************)

Require Import Coq.Lists.List.
Require Import Main.SystemF.FreeVar.
Require Import Main.SystemF.LocalClosure.
Require Import Main.SystemF.Name.
Require Import Main.SystemF.Syntax.
Require Import Main.Tactics.

Fixpoint eeSub e1 x1 e2 :=
  match e1 with
  | eFreeVar x2 => if nameEq x1 x2 then e2 else e1
  | eBoundVar _ => e1
  | eAbs t e3 => eAbs t (eeSub e3 x1 e2)
  | eApp e3 e4 => eApp (eeSub e3 x1 e2) (eeSub e4 x1 e2)
  | eTAbs e3 => eTAbs (eeSub e3 x1 e2)
  | eTApp e3 t => eTApp (eeSub e3 x1 e2) t
  end.

Fixpoint ttSub t1 x1 t2 :=
  match t1 with
  | tFreeVar x2 => if nameEq x1 x2 then t2 else t1
  | tBoundVar _ => t1
  | tArrow t3 t4 => tArrow (ttSub t3 x1 t2) (ttSub t4 x1 t2)
  | tForAll t3 => tForAll (ttSub t3 x1 t2)
  end.

Fixpoint etSub e1 x1 t1 :=
  match e1 with
  | eFreeVar _ => e1
  | eBoundVar _ => e1
  | eAbs t2 e2 => eAbs (ttSub t2 x1 t1) (etSub e2 x1 t1)
  | eApp e2 e3 => eApp (etSub e2 x1 t1) (etSub e3 x1 t1)
  | eTAbs e2 => eTAbs (etSub e2 x1 t1)
  | eTApp e2 t2 => eTApp (etSub e2 x1 t1) (ttSub t2 x1 t1)
  end.

(******************************************************************)
(* Substituting a non-free variable of a term/type has no effect. *)
(******************************************************************)

Theorem tttSubBound :
  forall t1 t2 x,
  ~ In x (tFreeVars t1) ->
  ttSub t1 x t2 = t1.
Proof.
  induction t1; magic.
Qed.

#[export] Hint Resolve tttSubBound : main.

Theorem eeeSubBound :
  forall e1 e2 x,
  ~ In x (eeFreeVars e1) ->
  eeSub e1 x e2 = e1.
Proof.
  induction e1; magic.
Qed.

#[export] Hint Resolve eeeSubBound : main.

Theorem eetSubBound :
  forall e t x,
  ~ In x (etFreeVars e) ->
  etSub e x t = e.
Proof.
  induction e; magic; clean; f_equal; magic; apply tttSubBound; magic.
Qed.

#[export] Hint Resolve eetSubBound : main.

(*****************************************)
(* Substitution preserves local closure. *)
(*****************************************)

Theorem ttSubLocallyClosed :
  forall i t1 t2 x,
  tLocallyClosed t1 i ->
  tLocallyClosed t2 i ->
  tLocallyClosed (ttSub t1 x t2) i.
Proof.
  clean. gen i. induction t1; magic; clean; invert H; magic.
  constructor. apply IHt1; magic.
  apply tLocalClosureMonotonic with (i1 := i); magic.
Qed.

#[export] Hint Resolve ttSubLocallyClosed : main.

Theorem eeSubLocallyClosed :
  forall e1 e2 ie it x,
  eLocallyClosed e1 ie it ->
  eLocallyClosed e2 ie it ->
  eLocallyClosed (eeSub e1 x e2) ie it.
Proof.
  clean. gen ie it. induction e1; magic; clean; invert H; magic;
    constructor; magic; apply IHe1; magic;
    apply eLocalClosureMonotonic with (ie1 := ie) (it1 := it); magic.
Qed.

#[export] Hint Resolve eeSubLocallyClosed : main.

Theorem etSubLocallyClosed :
  forall e ie it t x,
  eLocallyClosed e ie it ->
  tLocallyClosed t it ->
  eLocallyClosed (etSub e x t) ie it.
Proof.
  clean. gen ie it. induction e; magic; clean; invert H; magic.
  constructor. apply IHe; magic.
  apply tLocalClosureMonotonic with (i1 := it); magic.
Qed.

#[export] Hint Resolve etSubLocallyClosed : main.

(************************************)
(* Free variables of a substitution *)
(************************************)

#[local] Theorem inclAppRemoveWeakeningLeft :
  forall x l1 l2 l3,
  incl (l1 ++ remove nameEq x l2) (l1 ++ remove nameEq x (l2 ++ l3)).
Proof.
  unfold incl. clean.
  fact (in_app_or l1 (remove nameEq x l2) a H).
  destruct H0; magic.
  apply in_or_app. right.
  induction l2; magic.
Qed.

#[local] Hint Resolve inclAppRemoveWeakeningLeft : main.

#[local] Theorem inclAppRemoveWeakeningRight :
  forall x l1 l2 l3,
  incl (l1 ++ remove nameEq x l3) (l1 ++ remove nameEq x (l2 ++ l3)).
Proof.
  unfold incl. clean.
  fact (in_app_or l1 (remove nameEq x l3) a H).
  destruct H0; magic.
  apply in_or_app. right.
  induction l2; magic.
Qed.

#[local] Hint Resolve inclAppRemoveWeakeningRight : main.

Theorem tttFreeSub :
  forall t1 t2 x,
  incl
    (tFreeVars (ttSub t1 x t2))
    (tFreeVars t2 ++ remove nameEq x (tFreeVars t1)).
Proof.
  clean. induction t1; magic. clean. apply incl_app.
  - apply incl_tran with (
      m := tFreeVars t2 ++ remove nameEq x (tFreeVars t1_1)
    ); magic.
  - apply incl_tran with (
      m := tFreeVars t2 ++ remove nameEq x (tFreeVars t1_2)
    ); magic.
Qed.

#[export] Hint Resolve tttFreeSub : main.

Theorem eeeeFreeSub :
  forall e1 e2 x,
  incl
    (eeFreeVars (eeSub e1 x e2))
    (eeFreeVars e2 ++ remove nameEq x (eeFreeVars e1)).
Proof.
  clean. induction e1; magic. clean. apply incl_app.
  - apply incl_tran with (
      m := eeFreeVars e2 ++ remove nameEq x (eeFreeVars e1_1)
    ); magic.
  - apply incl_tran with (
      m := eeFreeVars e2 ++ remove nameEq x (eeFreeVars e1_2)
    ); magic.
Qed.

#[export] Hint Resolve eeeeFreeSub : main.

Theorem eeetFreeSub :
  forall e t x,
  incl (eeFreeVars (etSub e x t)) (eeFreeVars e).
Proof.
  clean. induction e; magic.
Qed.

#[export] Hint Resolve eeetFreeSub : main.

Theorem eteeFreeSub :
  forall e1 e2 x,
  incl (etFreeVars (eeSub e1 x e2)) (etFreeVars e2 ++ etFreeVars e1).
Proof.
  clean. induction e1; magic; clean; apply incl_app.
  - apply incl_tran with (m := etFreeVars e2 ++ tFreeVars t); magic.
  - apply incl_tran with (m := etFreeVars e2 ++ etFreeVars e1); magic.
  - apply incl_tran with (m := etFreeVars e2 ++ etFreeVars e1_1); magic.
  - apply incl_tran with (m := etFreeVars e2 ++ etFreeVars e1_2); magic.
  - apply incl_tran with (m := etFreeVars e2 ++ etFreeVars e1); magic.
  - apply incl_tran with (m := etFreeVars e1 ++ tFreeVars t); magic.
Qed.

#[export] Hint Resolve eteeFreeSub : main.

Theorem etetFreeSub :
  forall e t x,
  incl
    (etFreeVars (etSub e x t))
    (tFreeVars t ++ remove nameEq x (etFreeVars e)).
Proof.
  clean. induction e; magic; clean; apply incl_app.
  - apply incl_tran with (
      m := tFreeVars t ++ remove nameEq x (tFreeVars t0)
    ); magic.
  - apply incl_tran with (
      m := tFreeVars t ++ remove nameEq x (etFreeVars e)
    ); magic.
  - apply incl_tran with (
      m := tFreeVars t ++ remove nameEq x (etFreeVars e1)
    ); magic.
  - apply incl_tran with (
      m := tFreeVars t ++ remove nameEq x (etFreeVars e2)
    ); magic.
  - apply incl_tran with (
      m := tFreeVars t ++ remove nameEq x (etFreeVars e)
    ); magic.
  - apply incl_tran with (
      m := tFreeVars t ++ remove nameEq x (tFreeVars t0)
    ); magic.
Qed.

#[export] Hint Resolve etetFreeSub : main.

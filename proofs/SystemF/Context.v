(*****************************)
(*****************************)
(****                     ****)
(****   Typing contexts   ****)
(****                     ****)
(*****************************)
(*****************************)

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Main.SystemF.FreeVar.
Require Import Main.SystemF.LocalClosure.
Require Import Main.SystemF.Name.
Require Import Main.SystemF.Substitution.
Require Import Main.SystemF.Syntax.
Require Import Main.Tactics.

Import Coq.Lists.List.ListNotations.

Inductive context :=
| cEmpty : context
| cEExtend : context -> name -> type -> context
| cTExtend : context -> name -> context.

(*******************)
(* Variable lookup *)
(*******************)

Fixpoint eLookup c1 x1 :=
  match c1 with
  | cEmpty => None
  | cEExtend c2 x2 t => if nameEq x1 x2 then Some t else eLookup c2 x1
  | cTExtend c2 _ => eLookup c2 x1
  end.

Fixpoint tLookup c1 x1 :=
  match c1 with
  | cEmpty => false
  | cEExtend c2 _ _ => tLookup c2 x1
  | cTExtend c2 x2 => if nameEq x1 x2 then true else tLookup c2 x1
  end.

(***********)
(* Domains *)
(***********)

Fixpoint eDomain c1 :=
  match c1 with
  | cEmpty => []
  | cEExtend c2 x t => x :: eDomain c2
  | cTExtend c2 _ => eDomain c2
  end.

Fixpoint tDomain c1 :=
  match c1 with
  | cEmpty => []
  | cEExtend c2 _ _ => tDomain c2
  | cTExtend c2 x => x :: tDomain c2
  end.

(************************)
(* Type well-formedness *)
(************************)

Definition tWellFormed c t :=
  tLocallyClosed t 0 /\
  incl (tFreeVars t) (tDomain c).

(***************************)
(* Context well-formedness *)
(***************************)

Inductive cWellFormed : context -> Prop :=
| cwfEmpty :
  cWellFormed cEmpty
| cwfEExtend :
  forall c t x,
  ~ In x (eDomain c) ->
  tWellFormed c t ->
  cWellFormed c ->
  cWellFormed (cEExtend c x t)
| cwfTExtend :
  forall c x,
  ~ In x (tDomain c) ->
  cWellFormed c ->
  cWellFormed (cTExtend c x).

#[export] Hint Constructors cWellFormed : main.

(*****************************)
(* Concatenation of contexts *)
(*****************************)

Fixpoint cConcat c1 c2 :=
  match c2 with
  | cEmpty => c1
  | cEExtend c3 x t2 => cEExtend (cConcat c1 c3) x t2
  | cTExtend c3 x => cTExtend (cConcat c1 c3) x
  end.

(****************************)
(* Substitution on contexts *)
(****************************)

Fixpoint cSub c1 x1 t1 :=
  match c1 with
  | cEmpty => cEmpty
  | cEExtend c2 x2 t2 => cEExtend (cSub c2 x1 t1) x2 (ttSub t2 x1 t1)
  | cTExtend c2 x2 => cTExtend (cSub c2 x1 t1) x2
  end.

(***********************************)
(* Facts about domains and lookups *)
(***********************************)

Theorem eDomainLookup :
  forall c x,
  In x (eDomain c) <-> exists t, eLookup c x = Some t.
Proof.
  clean. split; induction c; eMagic. clean. destruct H; eMagic.
Qed.

#[export] Hint Resolve -> eDomainLookup : main.
#[export] Hint Resolve <- eDomainLookup : main.

Theorem tDomainLookup :
  forall c x,
  In x (tDomain c) <-> tLookup c x = true.
Proof.
  clean. induction c; magic.
Qed.

#[export] Hint Resolve -> tDomainLookup : main.
#[export] Hint Resolve <- tDomainLookup : main.

(************************************)
(* Facts about type well-formedness *)
(************************************)

Theorem tWellFormedClosed :
  forall c t x,
  tWellFormed c t ->
  In x (tFreeVars t) ->
  In x (tDomain c).
Proof.
  clean. apply tDomainLookup. invert H. magic.
Qed.

#[export] Hint Resolve tWellFormedClosed : main.

Theorem tLookupWellFormed :
  forall c x t,
  cWellFormed c ->
  eLookup c x = Some t ->
  tWellFormed c t.
Proof.
  clean. unfold tWellFormed. induction H; magic. clean.
  destruct (nameEq x x0); magic. clean. invert H0. magic.
Qed.

#[export] Hint Resolve tLookupWellFormed : main.

(****************************)
(* Facts about substitution *)
(****************************)

Theorem cSubEDomain :
  forall c x t,
  eDomain (cSub c x t) = eDomain c.
Proof.
  induction c; magic.
Qed.

#[export] Hint Resolve cSubEDomain : main.

Theorem cSubTDomain :
  forall c x t,
  tDomain (cSub c x t) = tDomain c.
Proof.
  induction c; magic.
Qed.

#[export] Hint Resolve cSubTDomain : main.

(*****************************************)
(* Facts about concatenation of contexts *)
(*****************************************)

Theorem cConcatEmpty : forall c, cConcat cEmpty c = c.
Proof.
  induction c; magic.
Qed.

#[export] Hint Resolve cConcatEmpty : main.

Theorem cConcatAssoc :
  forall c1 c2 c3,
  cConcat (cConcat c1 c2) c3 = cConcat c1 (cConcat c2 c3).
Proof.
  induction c2; induction c3; magic.
Qed.

#[export] Hint Resolve cConcatAssoc : main.

(*****************************************)
(* Facts about concatenation and domains *)
(*****************************************)

Theorem eDomainConcat :
  forall c1 c2,
  eDomain (cConcat c1 c2) = eDomain c2 ++ eDomain c1.
Proof.
  induction c2; magic.
Qed.

#[export] Hint Resolve eDomainConcat : main.

Theorem tDomainConcat :
  forall c1 c2,
  tDomain (cConcat c1 c2) = tDomain c2 ++ tDomain c1.
Proof.
  induction c2; magic.
Qed.

#[export] Hint Resolve tDomainConcat : main.

(****************************************)
(* Facts about concatenation and lookup *)
(****************************************)

Theorem cConcatELookup :
  forall c1 c2 t x,
  eLookup (cConcat c1 c2) x = Some t ->
  eLookup c1 x = Some t \/ eLookup c2 x = Some t.
Proof.
  induction c2; magic.
Qed.

#[export] Hint Resolve cConcatELookup : main.

Theorem cConcatTLookup :
  forall c1 c2 x,
  tLookup (cConcat c1 c2) x = true ->
  tLookup c1 x = true \/ tLookup c2 x = true.
Proof.
  induction c2; magic.
Qed.

#[export] Hint Resolve cConcatTLookup : main.

Theorem cELookupConcatRight :
  forall c1 c2 t x,
  eLookup c2 x = Some t ->
  eLookup (cConcat c1 c2) x = Some t.
Proof.
  induction c2; magic.
Qed.

#[export] Hint Resolve cELookupConcatRight : main.

Theorem cELookupConcatLeft :
  forall c1 c2 t x,
  eLookup c1 x = Some t ->
  eLookup c2 x = None ->
  eLookup (cConcat c1 c2) x = Some t.
Proof.
  induction c2; magic.
Qed.

#[export] Hint Resolve cELookupConcatLeft : main.

Theorem cTLookupConcatRight :
  forall c1 c2 x,
  tLookup c2 x = true ->
  tLookup (cConcat c1 c2) x = true.
Proof.
  induction c2; magic.
Qed.

#[export] Hint Resolve cTLookupConcatRight : main.

Theorem cTLookupConcatLeft :
  forall c1 c2 x,
  tLookup c1 x = true ->
  tLookup (cConcat c1 c2) x = true.
Proof.
  induction c2; magic.
Qed.

#[export] Hint Resolve cTLookupConcatLeft : main.

Theorem cELookupNone :
  forall c1 c2 t x,
  eLookup c1 x = Some t ->
  cWellFormed (cConcat c1 c2) ->
  eLookup c2 x = None.
Proof.
  clean. induction c2; magic; invert H0; feed IHc2; clean.
  destruct (nameEq x n); magic. clean.
  assert (In n (eDomain c1)); eMagic.
  rewrite eDomainConcat in H4.
  unfold not in H4. magic.
Qed.

#[export] Hint Resolve cELookupNone : main.

Theorem cTLookupNone :
  forall c1 c2 x,
  tLookup c1 x = true ->
  cWellFormed (cConcat c1 c2) ->
  tLookup c2 x = false.
Proof.
  clean. induction c2; magic; invert H0; feed IHc2; clean.
  destruct (nameEq x n); magic. clean.
  assert (In n (tDomain c1)); [eMagic | idtac].
  rewrite tDomainConcat in H3.
  unfold not in H3. magic.
Qed.

#[export] Hint Resolve cTLookupNone : main.

(***************************************)
(* Facts about context well-formedness *)
(***************************************)

Theorem cWellFormedESkip :
  forall c1 c2 t x,
  cWellFormed (cConcat (cEExtend c1 x t) c2) ->
  cWellFormed (cConcat c1 c2).
Proof.
  clean. induction c2; invert H; magic; clean; constructor; magic.
  - rewrite eDomainConcat in *. clean.
    unfold not in *. clean.
    pose proof (in_app_or (eDomain c2) (eDomain c1) n H).
    destruct H0; magic.
  - unfold tWellFormed in *. split; magic. clean.
    rewrite tDomainConcat in *. magic.
  - rewrite tDomainConcat in *. magic.
Qed.

#[export] Hint Resolve cWellFormedESkip : main.

Theorem cWellFormedTSkip :
  forall c1 c2 t x,
  cWellFormed (cConcat (cTExtend c1 x) c2) ->
  tWellFormed c1 t ->
  cWellFormed (cConcat c1 (cSub c2 x t)).
Proof.
  clean. induction c2; invert H; magic; clean; constructor; magic.
  - unfold tWellFormed in H5.
    rewrite eDomainConcat in *. rewrite cSubEDomain.
    unfold not in *. clean.
    assert (In n (eDomain c2) \/ In n (eDomain c1)); magic.
  - unfold tWellFormed in *. split; magic. clean.
    apply incl_tran with (
      m := tFreeVars t ++ remove nameEq x (tFreeVars t0)
    ); magic.
    rewrite tDomainConcat. rewrite tDomainConcat in H1.
    assert (
      incl
        (remove nameEq x (tFreeVars t0))
        (tDomain (cSub c2 x t) ++ tDomain c1)
    ); magic.
    rewrite cSubTDomain.
    unfold incl in *. clean.
    specialize (H1 a). feed H1.
    + pose proof (nameInRemove (tFreeVars t0) a x H3). magic.
    + pose proof (remove_In nameEq (tFreeVars t0) x).
      assert (a <> x); magic. clear H5.
      pose proof (in_app_or (tDomain c2) (x :: tDomain c1) a H1).
      destruct H5; magic.
  - rewrite tDomainConcat in *.
    unfold not in *. clean.
    assert (In n (tDomain (cSub c2 x t)) \/ In n (tDomain c1)); magic.
    destruct H1; magic.
    rewrite cSubTDomain in H1. magic.
Qed.

#[export] Hint Resolve cWellFormedTSkip : main.

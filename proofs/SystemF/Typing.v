(**************************)
(**************************)
(****                  ****)
(****   Typing rules   ****)
(****                  ****)
(**************************)
(**************************)

Require Import Coq.Bool.Bool.
Require Import Coq.Lists.List.
Require Import Main.SystemF.Context.
Require Import Main.SystemF.FreeVar.
Require Import Main.SystemF.LocalClosure.
Require Import Main.SystemF.Name.
Require Import Main.SystemF.Opening.
Require Import Main.SystemF.Syntax.
Require Import Main.Tactics.

Inductive hasType : context -> term -> type -> Prop :=
| htFreeVar :
  forall c t x,
  cWellFormed c ->
  eLookup c x = Some t ->
  hasType c (eFreeVar x) t
| htAbs :
  forall c e l t1 t2,
  (
    forall x,
    ~ In x l ->
    hasType (cEExtend c x t2) (eeOpen e 0 (eFreeVar x)) t1
  ) ->
  hasType c (eAbs t2 e) (tArrow t2 t1)
| htApp :
  forall c e1 e2 t1 t2,
  hasType c e1 (tArrow t2 t1) ->
  hasType c e2 t2 ->
  hasType c (eApp e1 e2) t1
| htTAbs :
  forall c e l t,
  (
    forall x,
    ~ In x l ->
    hasType (cTExtend c x) (etOpen e 0 (tFreeVar x)) (ttOpen t 0 (tFreeVar x))
  ) ->
  hasType c (eTAbs e) (tForAll t)
| htTApp :
  forall c e t1 t2,
  tWellFormed c t2 ->
  hasType c e (tForAll t1) ->
  hasType c (eTApp e t2) (ttOpen t1 0 t2).

#[export] Hint Constructors hasType : main.

(*****************************************)
(* The regularity of the typing judgment *)
(*****************************************)

Theorem typingRegularity :
  forall c e t,
  hasType c e t ->
  cWellFormed c /\ tWellFormed c t /\ eLocallyClosed e 0 0.
Proof.
  clean. induction H; clean.
  - split; magic. split; magic. unfold tWellFormed.
    split; induction H; magic; unfold tWellFormed in H1; magic; clean.
    destruct (nameEq x x0); magic. invert H0. magic.
  - pose proof (nameFresh l). clean. specialize (H0 x H1). clean. split.
    + invert H0. magic.
    + split.
      * constructor; clean.
        -- constructor.
           ++ invert H0. unfold tWellFormed in H8. magic.
           ++ unfold tWellFormed in H2. magic.
        -- invert H0.
           unfold tWellFormed in H8.
           unfold tWellFormed in H2.
           magic.
      * constructor.
        -- invert H0. unfold tWellFormed in H8. magic.
        -- apply eeLocallyClosedOpen with (e2 := eFreeVar x). magic.
  - split; magic. split; magic.
    unfold tWellFormed in H5. clean. invert H5. constructor; eMagic.
  - pose proof (nameFresh (l ++ tFreeVars t)). clean.
    specialize (H0 x). feed H0. clean. split.
    + invert H0. magic.
    + split.
      * constructor; clean.
        -- constructor. invert H2.
           apply ttLocallyClosedOpen with (t2 := tFreeVar x). magic.
        -- invert H2. clean. unfold incl in *. clean.
           specialize (H5 a). feed H5. apply tttFreeOpen. magic.
      * constructor. apply etLocallyClosedOpen with (t := tFreeVar x). magic.
  - split; magic. unfold tWellFormed in H. clean. split; magic.
    constructor.
    + unfold tWellFormed in H2. apply locallyClosedOpenForAll; magic.
    + apply incl_tran with (m := tFreeVars t2 ++ tFreeVars t1).
      * apply tttFreeOpen.
      * unfold tWellFormed in H2. magic.
Qed.

#[export] Hint Resolve typingRegularity : main.

(*********************)
(* Context weakening *)
(*********************)

Theorem contextWeakening :
  forall c1 c2 c3 e t,
  hasType (cConcat c1 c3) e t ->
  cWellFormed (cConcat (cConcat c1 c2) c3) ->
  hasType (cConcat (cConcat c1 c2) c3) e t.
Proof.
  clean. remember (cConcat c1 c3). outro c3. induction H; eMagic; clean.
  - rewrite cConcatAssoc in *. constructor; magic.
    pose proof (cConcatELookup c1 c3 t x H0). eMagic.
  - apply htAbs with (l := l ++ eDomain c3 ++ eDomain c2 ++ eDomain c1). clean.
    specialize (H0 x). clean.
    specialize (H0 (cEExtend c3 x t2)). clean.
    apply H0.
    constructor; magic.
    + do 2 rewrite eDomainConcat. magic.
    + pose proof (
        typingRegularity
        (cEExtend (cConcat c1 c3) x t2)
        (eeOpen e 0 (eFreeVar x))
        t1
      ). clean.
      invert H3.
      unfold tWellFormed in *. clean. split; magic.
      rewrite tDomainConcat in H6.
      do 2 rewrite tDomainConcat.
      unfold incl in *. clean.
      specialize (H6 a). clean.
      assert (In a (tDomain c3) \/ In a (tDomain c1)); magic.
  - apply htTAbs with (l := l ++ tDomain c3 ++ tDomain c2 ++ tDomain c1).
    clean.
    specialize (H0 x). clean.
    specialize (H0 (cTExtend c3 x)). clean.
    apply H0.
    constructor; magic.
    do 2 rewrite tDomainConcat. magic.
  - constructor; magic.
    pose proof (typingRegularity (cConcat c1 c3) e (tForAll t1)). clean.
    unfold tWellFormed in H. clean.
    constructor; magic.
    rewrite tDomainConcat in H5.
    do 2 rewrite tDomainConcat.
    unfold incl in *. clean.
    specialize (H5 a). clean.
    assert (In a (tDomain c3) \/ In a (tDomain c1)); magic.
Qed.

#[export] Hint Resolve contextWeakening : main.

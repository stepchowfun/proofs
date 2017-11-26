(*********************************************************************)
(*********************************************************************)
(****                                                             ****)
(****   A proof that the simply typed lambda calculus is sound.   ****)
(****                                                             ****)
(*********************************************************************)
(*********************************************************************)

(***************)
(* Identifiers *)
(***************)

Parameter id : Set.
Axiom idEqDec : forall (id1 id2 : id), {id1 = id2} + {id1 <> id2}.

(**********)
(* Syntax *)
(**********)

Inductive term : Set :=
| eUnit : term
| eVar : id -> term
| eAbs : id -> type -> term -> term
| eApp : term -> term -> term

with type : Set :=
| tUnit : type
| tArrow : type -> type -> type.

(******************)
(* Free variables *)
(******************)

Inductive freeVar : term -> id -> Prop :=
| fVar :
  forall x,
  freeVar (eVar x) x
| fAbs :
  forall e x1 x2 t,
  freeVar e x1 ->
  x1 <> x2 ->
  freeVar (eAbs x2 t e) x1
| fApp :
  forall x e1 e2,
  freeVar e1 x \/ freeVar e2 x ->
  freeVar (eApp e1 e2) x.

Definition closed e := forall x, ~ freeVar e x.

(**********)
(* Typing *)
(**********)

Inductive context :=
| cEmpty : context
| cExtend : context -> id -> type -> context.

Fixpoint lookupVar c1 x1 :=
  match c1 with
  | cEmpty => None
  | cExtend c2 x2 t =>
    match idEqDec x1 x2 with
    | left _ => Some t
    | right _ => lookupVar c2 x1
    end
  end.

Inductive hasType : context -> term -> type -> Prop :=
| htUnit :
  forall c,
  hasType c eUnit tUnit
| htVar :
  forall x t c,
  lookupVar c x = Some t ->
  hasType c (eVar x) t
| htAbs :
  forall e x t1 t2 c,
  hasType (cExtend c x t1) e t2 ->
  hasType c (eAbs x t1 e) (tArrow t1 t2)
| htApp :
  forall e1 e2 t1 t2 c,
  hasType c e1 t1 ->
  hasType c e2 (tArrow t1 t2) ->
  hasType c (eApp e2 e1) t2.

(*************************)
(* Operational semantics *)
(*************************)

Inductive value : term -> Prop :=
| vUnit : value eUnit
| vAbs : forall e x t, value (eAbs x t e).

(* NOTE: This function assumes e2 is a closed term. *)

Fixpoint sub e1 x1 e2 :=
  match e1 with
  | eUnit => e1
  | eVar x2 =>
    match idEqDec x1 x2 with
    | left _ => e2
    | right _ => e1
    end
  | eAbs x2 t e3 =>
    match idEqDec x1 x2 with
    | left _ => e1
    | right _ => eAbs x2 t (sub e3 x1 e2)
    end
  | eApp e3 e4 => eApp (sub e3 x1 e2) (sub e4 x1 e2)
  end.

Inductive step : term -> term -> Prop :=
| sBeta :
  forall e1 e2 x t,
  value e2 ->
  step (eApp (eAbs x t e1) e2) (sub e1 x e2)
| sApp1 :
  forall e1 e2 e3,
  step e1 e2 ->
  step (eApp e1 e3) (eApp e2 e3)
| sApp2 :
  forall e1 e2 e3,
  value e1 ->
  step e2 e3 ->
  step (eApp e1 e2) (eApp e1 e3).

Inductive stepStar : term -> term -> Prop :=
| scRefl :
  forall e,
  stepStar e e
| scStep :
  forall e1 e2 e3,
  step e1 e2 ->
  stepStar e2 e3 ->
  stepStar e1 e3.

Definition normalForm e1 := ~ exists e2, step e1 e2.

(************)
(* Progress *)
(************)

Theorem progress :
  forall e1 t,
  hasType cEmpty e1 t ->
  value e1 \/ exists e2, step e1 e2.
Proof.
  intros e t H1.
  remember cEmpty as c1 eqn:H2 in H1.
  induction H1 as [
    c1                         | (* htUnit *)
    x t c1 H3                  | (* htVar *)
    e x t1 t2 c1 H3 H4         | (* htAbs *)
    e1 e2 t1 t2 c1 H3 H4 H5 H6   (* htApp *)
   ].
  (* htUnit *)
  - left.
    apply vUnit.
  (* htVar *)
  - rewrite H2 in H3.
    simpl in H3.
    inversion H3.
  (* htAbs *)
  - left.
    apply vAbs.
   (* htApp *)
  - right.
    specialize (H4 H2).
    specialize (H6 H2).
    destruct H6 as [H6 | H6].
    + destruct H4 as [H4 | H4].
      * {
        inversion H5 as [
                                          | (* htUnit *)
          x1 t3 c2 H7 H8 H9 H10           | (* htVar *)
          e3 x1 t3 t4 c2 H7 H8 H9 H10     | (* htAbs *)
          e3 e4 t3 t4 c2 H7 H8 H9 H10 H11   (* htApp *)
        ].
        (* htUnit *)
        (* htVar *)
        - inversion H6 as [
          H11          | (* vUnit *)
          x2 t4 e3 H11   (* vAbs *)
        ]; rewrite <- H11 in H9; inversion H9.
        (* htAbs *)
        - exists (sub e3 x1 e1).
          apply sBeta.
          auto.
        (* htApp *)
        - inversion H6 as [
          H12         | (* vUnit *)
          x t5 e5 H12   (* vAbs *)
        ]; rewrite <- H12 in H10; inversion H10.
      }
      * destruct H4 as [e3 H4].
        exists (eApp e2 e3).
        apply sApp2; auto.
    + destruct H6 as [e3 H6].
      exists (eApp e3 e1).
      apply sApp1.
      auto.
Qed.

(****************)
(* Preservation *)
(****************)

Lemma typingJudgmentClosed :
  forall c e t1 x,
  hasType c e t1 ->
  freeVar e x ->
  exists t2,
  lookupVar c x = Some t2.
Proof.
  intros c1 e1 t1 x1 H1 H2.
  induction H1 as [
    c2                         | (* htUnit *)
    x2 t2 c2 H3                | (* htVar *)
    e2 x2 t2 t3 c2 H3 H4       | (* htAbs *)
    e2 e3 t2 t3 c2 H3 H4 H5 H6   (* htApp *)
  ].
  (* htUnit *)
  - inversion H2.
  (* htVar *)
  - inversion H2 as [
      x3 H4 H5 | (* fVar *)
               | (* fAbs *)
                 (* fApp *)
    ].
    rewrite H5 in *.
    exists t2.
    auto.
  (* htApp *)
  - inversion H2 as [
                              | (* fVar *)
      e3 x3 x4 t4 H5 H6 H7 H8 | (* fAbs *)
                                (* fApp *)
    ].
    specialize (H4 H5).
    destruct H4 as [t5 H4].
    simpl in H4.
    destruct (idEqDec x1 x2).
    + contradiction.
    + exists t5.
      auto.
  (* htAbs *)
  - inversion H2 as [
                        | (* fVar *)
                        | (* fAbs *)
      x2 e4 e5 H7 H8 H9   (* fApp *)
    ].
    destruct H7 as [H7 | H7].
    + specialize (H6 H7).
      destruct H6 as [t4 H6].
      exists t4.
      auto.
    + specialize (H4 H7).
      destruct H4 as [t4 H4].
      exists t4.
      auto.
Qed.

Lemma contextInvariance :
  forall c1 c2 e t,
  hasType c1 e t ->
  (forall x, freeVar e x -> lookupVar c1 x = lookupVar c2 x) ->
  hasType c2 e t.
Proof.
  intros c1 c2 e1 t1 H1.
  generalize dependent c2.
  induction H1 as [
    c1                         | (* htUnit *)
    x1 t c1 H1                 | (* htVar *)
    e1 x1 t1 t2 c1 H1 H2       | (* htAbs *)
    e1 e2 t1 t2 c1 H1 H2 H3 H4   (* htApp *)
  ].
  (* htUnit *)
  - intros c2 H.
    apply htUnit.
  (* htVar *)
  - intros c2 H2.
    apply htVar.
    specialize (H2 x1).
    specialize (H2 (fVar x1)).
    rewrite <- H2.
    rewrite H1.
    reflexivity.
  (* htAbs *)
  - intros c2 H3.
    apply htAbs.
    apply H2.
    intros x2 H4.
    specialize (H3 x2).
    simpl.
    destruct (idEqDec x2 x1).
    + reflexivity.
    + apply H3.
      apply fAbs; auto.
  (* htApp *)
  - intros c2 H5.
    apply htApp with (t1 := t1) (t2 := t2).
    + apply H2.
      intros x1 H6.
      apply H5.
      apply fApp.
      auto.
    + apply H4.
      intros x1 H6.
      apply H5.
      apply fApp.
      auto.
Qed.

Theorem substitutionPreservesTyping :
  forall c x e1 e2 t1 t2,
  hasType (cExtend c x t1) e2 t2 ->
  hasType cEmpty e1 t1 ->
  hasType c (sub e2 x e1) t2.
Proof.
  intros c1 x1 e1 e2 t1 t2 H1 H2.
  generalize dependent c1.
  generalize dependent t2.
  induction e2 as [
                | (* eUnit *)
    x2          | (* eVar *)
    x2 t3 e3 H3 | (* eAbs *)
    e3 H3 e4 H4   (* eApp *)
  ]; intros t2 c1 H1.
  (* eUnit *)
  - simpl.
    inversion H1 as [
      c2 H3 H4 H5 | (* htUnit *)
                  | (* htVar *)
                  | (* htAbs *)
                    (* htApp *)
    ].
    apply htUnit.
  (* eVar *)
  - simpl.
    inversion H1 as [
                           | (* htUnit *)
      x3 t3 c2 H3 H4 H5 H6 | (* htVar *)
                           | (* htAbs *)
                             (* htApp *)
    ].
    simpl in H3.
    destruct (idEqDec x1 x2) as [H7 | H7].
    + destruct (idEqDec x2 x1) as [H8 | H8].
      * {
        inversion H3 as [H9].
        rewrite <- H9.
        apply contextInvariance with (c1 := cEmpty).
        - auto.
        - intros x4 H10.
          assert (exists t, lookupVar cEmpty x4 = Some t) as H11.
          + apply typingJudgmentClosed with (e := e1) (t1 := t1); auto.
          + destruct H11 as [t4 H11].
            inversion H11.
      }
      * congruence.
    + destruct (idEqDec x2 x1) as [H8 | H8].
      * congruence.
      * apply htVar.
        auto.
  (* eAbs *)
  - simpl.
    destruct (idEqDec x1 x2) as [H4 | H4].
    + rewrite <- H4 in *. clear H4.
      apply contextInvariance with (c1 := cExtend c1 x1 t1).
      * auto.
      * {
        intros x3 H4.
        simpl.
        destruct (idEqDec x3 x1) as [H5 | H5].
        - inversion H4 as [
                                    | (* fVar *)
            e4 x4 x5 t4 H6 H7 H8 H9 | (* fAbs *)
                                      (* fApp *)
          ].
          contradiction.
        - reflexivity.
      }
    + inversion H1 as [
                                   | (* htUnit *)
                                   | (* htVar *)
        e4 x3 t4 t5 c2 H5 H6 H7 H8 | (* htAbs *)
                                     (* htApp *)
      ].
      apply htAbs.
      apply H3.
      apply contextInvariance with (c1 := cExtend (cExtend c1 x1 t1) x2 t3).
      * auto.
      * {
        intros x4 H9.
        simpl.
        destruct (idEqDec x4 x2) as [H10 | H10].
        - destruct (idEqDec x4 x1) as [H11 | H11].
          + congruence.
          + reflexivity.
        - reflexivity.
      }
  (* eApp *)
  - inversion H1 as [
                                    | (* htUnit *)
                                    | (* htVar *)
                                    | (* htAbs *)
      e5 e6 t3 t4 c2 H5 H6 H7 H8 H9   (* htApp *)
    ].
    simpl.
    apply htApp with (t1 := t3) (t2 := t2).
    + apply H4.
      auto.
    + apply H3.
      auto.
Qed.

Theorem preservation :
  forall e1 e2 t,
  hasType cEmpty e1 t ->
  step e1 e2 ->
  hasType cEmpty e2 t.
Proof.
  remember cEmpty as c1 eqn:H1.
  intros e1 e2 t H2.
  generalize dependent e2.
  induction H2 as [
     c1                         | (* htUnit *)
     x t c1 H2                  | (* htVar *)
     e1 x t1 t2 c1 H2 H3        | (* htAbs *)
     e1 e2 t1 t2 c1 H2 H3 H4 H5   (* htApp *)
   ].
   (* htUnit *)
   - intros e H2. inversion H2.
   (* htVar *)
   - intros e H3. inversion H3.
   (* htAbs *)
   - intros e H4. inversion H4.
   (* htApp *)
   - intros e3 H6.
     rewrite H1 in *.
     clear c1 H1.
     specialize (H3 eq_refl).
     specialize (H5 eq_refl).
     inversion H6 as [
       x1 t3 e4 e5 H7 H8 H9  | (* sBeta *)
       e4 e5 e6 H7 H8 H9     | (* sApp1 *)
       e4 e5 e6 H7 H8 H9 H10   (* sApp2 *)
     ].
     (* sBeta *)
     + apply substitutionPreservesTyping with (t1 := t1).
       * rewrite <- H8 in H4.
         inversion H4 as [
                                          | (* htUnit *)
                                          | (* htVar *)
           e6 x2 t4 t5 c1 H10 H11 H12 H13 | (* htAbs *)
                                            (* htApp *)
         ].
         auto.
       * auto.
     (* sApp1 *)
     + apply htApp with (t1 := t1) (t2 := t2).
       * auto.
       * apply H5.
         auto.
     (* sApp2 *)
     + apply htApp with (t1 := t1) (t2 := t2); auto.
Qed.

(*************)
(* Soundness *)
(*************)

Definition stuck e := normalForm e /\ ~ value e.

Theorem soundness :
  forall e1 e2 t,
  hasType cEmpty e1 t ->
  stepStar e1 e2 ->
  ~ stuck e2.
Proof.
  intros e1 e2 t H1 H2.
  unfold not.
  unfold stuck.
  unfold normalForm.
  intros H3.
  destruct H3 as [H3 H4].
  assert (hasType cEmpty e2 t) as H5.
  - induction H2 as [
      e3                | (* scRefl *)
      e3 e4 e5 H5 H6 H7   (* scStep *)
    ].
    (* scRefl *)
    + auto.
    (* scStep *)
    + assert (hasType cEmpty e4 t) as H8.
      * apply preservation with (e1 := e3); auto.
      * apply H7; auto.
  - assert (value e2 \/ exists e3, step e2 e3) as H6.
    + apply progress with (t := t).
      auto.
    + destruct H6 as [H6 | H6]; auto.
Qed.

(****************************************************************)
(****************************************************************)
(****                                                        ****)
(****   A formalization of the function extensionality and   ****)
(****   univalence axioms                                    ****)
(****                                                        ****)
(****************************************************************)
(****************************************************************)

Require Import Stdlib.Program.Basics.

#[local] Open Scope program_scope.
#[local] Open Scope type.

(* A universe to be univalent *)

Definition U := Type.

(* The groupoid structure of types *)

Definition inv [A] [x y : A] (p : x = y) : y = x :=
  match p in _ = z return z = x with
  | eq_refl => eq_refl
  end.

Definition concat [A] [x y z : A] (p : x = y) (q : y = z) : x = z :=
  match q in _ = z return x = z with
  | eq_refl => p
  end.

Definition left_refl [A] [x y : A] (p : x = y) : concat eq_refl p = p :=
  match p return concat eq_refl p = p with
  | eq_refl => eq_refl
  end.

Definition right_refl [A] [x y : A] (p : x = y) : concat p eq_refl = p :=
  eq_refl.

Definition left_inv [A] [x y : A] (p : x = y) : concat (inv p) p = eq_refl :=
  match p return concat (inv p) p = eq_refl with
  | eq_refl => eq_refl
  end.

Definition right_inv [A] [x y : A] (p : x = y) : concat p (inv p) = eq_refl :=
  match p return concat p (inv p) = eq_refl with
  | eq_refl => eq_refl
  end.

Definition assoc [A] [x y z w : A] (p : x = y) (q : y = z) (r : z = w) :
  concat (concat p q) r = concat p (concat q r) :=
  match r return concat (concat p q) r = concat p (concat q r) with
  | eq_refl =>
    match q return concat p q = concat p q with
    | eq_refl => eq_refl
    end
  end.

(* Transport *)

Definition transport [A] [x y : A] [P : A -> Type] (p : x = y) (px : P x) : P y
:=
  match p in _ = z return P z with
  | eq_refl => px
  end.

(* Action on paths *)

Definition ap [A B] [x y : A] (f : A -> B) (p : x = y) : f x = f y :=
  match p in _ = z return f x = f z with
  | eq_refl => eq_refl
  end.

Definition ap_refl [A B] (x : A) (f : A -> B) :
  ap f eq_refl = @eq_refl _ (f x)
:= eq_refl.

Definition ap_concat [A B] [x y z : A] (f : A -> B) (p : x = y) (q : y = z) :
  ap f (concat p q) = concat (ap f p) (ap f q)
:=
  match q with
  | eq_refl => eq_refl
  end.

Definition ap_inv [A B] [x y : A] (f : A -> B) (p : x = y) :
  ap f (inv p) = inv (ap f p)
:=
  match p with
  | eq_refl => eq_refl
  end.

Definition ap_compose [A B C] [x y : A] (f : A -> B) (g : B -> C) (p : x = y) :
  ap g (ap f p) = ap (g ∘ f) p
:=
  match p with
  | eq_refl => eq_refl
  end.

Definition ap_id [A] [x y : A] (p : x = y) : ap id p = p
:=
  match p with
  | eq_refl => eq_refl
  end.

(* Homotopy *)

Definition Homotopy [A] [B : A -> Type] (f g : forall x : A, B x) :=
  forall x, f x = g x.

Definition naturality
  [A B]
  [x y : A]
  (f g : A -> B)
  (h : Homotopy f g)
  (p : x = y)
: concat (ap f p) (h y) = concat (h x) (ap g p)
:=
  match p in _ = z return concat (ap f p) (h z) = concat (h x) (ap g p) with
  | eq_refl => left_refl _
  end.

(* Equivalence *)

Definition IsEquiv [A B] (f : A -> B) := {
  g : B -> A & {
  eta : Homotopy (g ∘ f) id & {
  epsilon : Homotopy (f ∘ g) id &
  forall x, ap f (eta x) = epsilon (f x) }}}.

(* Function extensionality *)

Definition path_to_homotopy [A] [B : A -> Type]
  (f g : forall x : A, B x) (p : f = g) :
  Homotopy f g :=
  fun x =>
    match p in _ = h return f x = h x with
    | eq_refl => eq_refl
    end.

Axiom function_extensionality :
  forall (A : U) (B : A -> U) (f g : forall x : A, B x),
  IsEquiv (path_to_homotopy f g).

(* Univalence *)

Definition path_to_equiv [A B] (p : A = B) :
  { f : A -> B & IsEquiv f } :=
  existT (@IsEquiv A B) (transport p)
    match p with
    | eq_refl =>
      existT _ id (
        existT _ (@eq_refl _) (existT _ (@eq_refl _) (fun _ => eq_refl))
      )
    end.

Axiom univalence : forall A B : U, IsEquiv (@path_to_equiv A B).

(* Homotopy n-types (starting at 0 rather than the more conventional -2) *)

Fixpoint IsTrunc n (A : Type) :=
  match n with
  | O => { c : A & forall x, c = x }
  | S p => forall x y : A, IsTrunc p (x = y)
  end.

Definition IsContr := IsTrunc 0.
Definition IsProp := IsTrunc 1.
Definition IsSet := IsTrunc 2.

Theorem is_trunc_cumulative : forall n A, IsTrunc n A -> IsTrunc (1 + n) A.
Proof.
  induction n.
  - unfold IsTrunc.
    cbn.
    intros.
    destruct X.
    exists (eq_trans (eq_sym (e x)) (e y)).
    intro.
    destruct x1, (e x).
    reflexivity.
  - cbn in *.
    intros.
    apply IHn.
    apply X.
Qed.

Theorem proof_irrelevance_is_prop :
  forall A, (forall x y : A, x = y) -> IsProp A.
Proof.
  unfold IsProp, IsTrunc.
  intros.
  exists (H x y).
  destruct x0.
  assert (forall x y (p : x = y), H x y = concat p (H y y)).
  - intros.
    destruct p.
    rewrite left_refl.
    reflexivity.
  - specialize (H0 _ _ (H x x)).
    assert (
      forall (x y z : A) (p : x = y) (q r : y = z),
      concat p q = concat p r -> q = r
    ).
    + intros.
      destruct p.
      do 2 rewrite left_refl in H1.
      assumption.
    + specialize (H1 _ _ _ (H x x) (H x x) eq_refl).
      auto.
Qed.

Theorem is_truncated_is_prop : forall n A, IsProp (IsTrunc n A).
Proof.
  induction n; intros; apply proof_irrelevance_is_prop; intros.
  - unfold IsTrunc in *.
    destruct x, y.
    destruct (e0 x).
    assert (e = e0).
    + assert (IsProp A).
      * apply proof_irrelevance_is_prop.
        intros.
        rewrite <- (e x).
        rewrite <- (e y).
        reflexivity.
      * destruct (function_extensionality _ _ e e0).
        destruct s.
        apply x.
        unfold Homotopy.
        intro.
        pose proof (is_trunc_cumulative 1 A X).
        destruct (X0 x0 x2 (e x2) (e0 x2)).
        auto.
    + rewrite H.
      reflexivity.
  - destruct (function_extensionality _ _ x y).
    destruct s.
    apply x0.
    unfold Homotopy.
    intro.
    destruct (function_extensionality _ _ (x x2) (y x2)).
    destruct s.
    apply x3.
    unfold Homotopy.
    intro.
    apply IHn.
Qed.

(* Quasi-inverse *)

Definition QuasiInv [A B] (f : A -> B) :=
  { g : B -> A & Homotopy (g ∘ f) id * Homotopy (f ∘ g) id }.

Theorem quasi_inverse_to_equiv :
  forall A B (f : A -> B), QuasiInv f -> IsEquiv f.
Proof.
  intros.
  destruct X, p.
  rename x into g.
  rename h into eta.
  rename h0 into epsilon.
  exists g.
  exists eta.
  exists (fun y =>
    concat (inv (epsilon (f (g y)))) (concat (ap f (eta (g y))) (epsilon y))
  ).
  intro.
  replace (eta (g (f x))) with (ap (g ∘ f) (eta x)).
  - replace (
      concat
        (@ap A B ((g ∘ f) (g (f x))) (@id A (g (f x))) f
          (@ap A A ((g ∘ f) x) (@id A x) (g ∘ f) (eta x)))
        (epsilon (f x))
    ) with (concat (epsilon (f (g (f x)))) (ap f (eta x))).
    + rewrite <- assoc.
      rewrite left_inv.
      rewrite left_refl.
      reflexivity.
    + pose proof naturality.
      specialize H with (h := fun x => epsilon (f x)) (p := eta x).
      unfold id, compose in *.
      change (ap f (eta x)) with (ap (fun x : A => f x) (eta x)).
      rewrite <- H.
      rewrite (ap_compose (fun x0 : A => g (f x0)) f).
      reflexivity.
  - change (g (f x)) with ((g ∘ f) x).
    pose proof naturality.
    specialize H with (h := eta) (p := eta x).
    change (eta (id x)) with (eta x) in H.
    replace (ap id (eta x)) with (eta x) in H.
    + assert (
        concat (concat (ap (g ∘ f) (eta x)) (eta x)) (inv (eta x)) =
        concat (concat (eta ((g ∘ f) x)) (eta x)) (inv (eta x))
      ).
      * unfold id.
        unfold id in H.
        rewrite H.
        reflexivity.
      * do 2 rewrite assoc in H0.
        do 2 rewrite right_inv in H0.
        exact H0.
    + set (p := eta x).
      destruct p.
      reflexivity.
Qed.

Definition equiv_to_quasi_inverse A B (f : A -> B) (e : IsEquiv f) : QuasiInv f
:= existT _ (projT1 e) (projT1 (projT2 e), projT1 (projT2 (projT2 e))).

(* The fibers of an equivalence are contractible *)

Definition fiber [A B] (f : A -> B) y := { x & f x = y }.

Theorem fiber_contr :
  forall A B (f : A -> B) y, IsEquiv f -> IsContr (fiber f y).
Proof.
  intros.
  unfold IsContr, IsTrunc.
  destruct X.
  do 2 destruct s.
  exists (existT _ (x y) (x1 y)).
  intros.
  destruct x2.
  assert (
    forall A B (f : A -> B) y (f1 f2 : fiber f y) (p : projT1 f1 = projT1 f2),
    concat (ap f p) (projT2 f2) = projT2 f1 ->
    f1 = f2
  ).
  - intros.
    destruct f1, f2.
    cbn in p, H.
    destruct p.
    rewrite left_refl in H.
    rewrite H.
    reflexivity.
  - apply H with (p := concat (ap x (inv e0)) (x0 x2)).
    cbn.
    rewrite ap_concat.
    specialize (e x2).
    unfold id, compose in e.
    unfold id.
    rewrite e.
    rewrite ap_compose.
    pose proof naturality.
    specialize H0 with (h := x1) (p := inv e0).
    unfold id in H0.
    unfold compose in *.
    rewrite H0.
    rewrite assoc.
    rewrite ap_id.
    rewrite left_inv.
    reflexivity.
Qed.

(* An example of using univalence *)

Inductive Bit : U :=
| Zero
| One.

Inductive Weekend : U :=
| Saturday
| Sunday.

Definition weekend_to_bit x :=
  match x with
  | Saturday => Zero
  | Sunday => One
  end.

Definition bit_to_weekend x :=
  match x with
  | Zero => Saturday
  | One => Sunday
  end.

Theorem weekend_bit_equiv : IsEquiv weekend_to_bit.
Proof.
  apply quasi_inverse_to_equiv.
  exists bit_to_weekend.
  split; intro; destruct x; reflexivity.
Qed.

Definition weekend_bit_path : Weekend = Bit :=
  projT1 (univalence _ _) (existT _ _ weekend_bit_equiv).

Definition invert_weekend x :=
  match x with
  | Saturday => Sunday
  | Sunday => Saturday
  end.

Theorem invert_weekend_involution x : invert_weekend (invert_weekend x) = x.
Proof.
  destruct x; auto.
Qed.

Definition invert_weekend_with_theorem :=
  exist (fun invert => forall x, invert (invert x) = x)
    invert_weekend
    invert_weekend_involution.

Definition invert_bit_with_theorem :=
  match weekend_bit_path in _ = A
  return { invert : A -> A | forall x, invert (invert x) = x } with
  | eq_refl => invert_weekend_with_theorem
  end.

Definition invert_bit : Bit -> Bit :=
  proj1_sig invert_bit_with_theorem.

Definition invert_bit_involution : forall x, invert_bit (invert_bit x) = x :=
  proj2_sig invert_bit_with_theorem.

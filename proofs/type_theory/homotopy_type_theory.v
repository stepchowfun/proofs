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

Definition left_id [A] [x y : A] (p : x = y) : concat eq_refl p = p :=
  match p return concat eq_refl p = p with
  | eq_refl => eq_refl
  end.

Definition right_id [A] [x y : A] (p : x = y) : concat p eq_refl = p :=
  match p return concat p eq_refl = p with
  | eq_refl => eq_refl
  end.

Definition left_inv [A] [x y : A] (p : x = y) :
  concat (inv p) p = eq_refl
:=
  match p return concat (inv p) p = eq_refl with
  | eq_refl => eq_refl
  end.

Definition right_inv [A] [x y : A] (p : x = y) :
  concat p (inv p) = eq_refl
:=
  match p return concat p (inv p) = eq_refl with
  | eq_refl => eq_refl
  end.

Definition assoc [A] [x y z w : A]
  (p : x = y) (q : y = z) (r : z = w)
: concat (concat p q) r = concat p (concat q r)
:=
  match r return concat (concat p q) r = concat p (concat q r) with
  | eq_refl =>
    match q return concat p q = concat p q with
    | eq_refl => eq_refl
    end
  end.

(* Transport *)

Definition transport [A] [x y : A] [P : A -> Type] (p : x = y) (px : P x)
:=
  match p in _ = z return P z with
  | eq_refl => px
  end.

(* Homotopy *)

Definition Homotopy [A] [B : A -> Type] (f g : forall x : A, B x) :=
  forall x, f x = g x.

(* Equivalence *)

Definition IsEquiv [A B] (f : A -> B) :=
  { g : B -> A & Homotopy (f ∘ g) id } *
  { g : B -> A & Homotopy (g ∘ f) id }.

(* Quasi-inverse *)

Definition QuasiInv [A B] (f : A -> B) :=
  { g : B -> A & Homotopy (f ∘ g) id * Homotopy (g ∘ f) id }.

(* Equivalence is logically equivalent to quasi-inverse. *)

Theorem quasi_inverse_to_equiv :
  forall A B (f : A -> B), QuasiInv f -> IsEquiv f.
Proof.
  intros.
  destruct X, p.
  split; exists x; auto.
Qed.

Theorem equiv_to_quasi_inverse :
  forall A B (f : A -> B), IsEquiv f -> QuasiInv f.
Proof.
  unfold IsEquiv, QuasiInv, Homotopy, compose, id.
  intros.
  destruct X, s, s0.
  exists (fun y => x0 (f (x y))).
  split; intros.
  - rewrite e0.
    auto.
  - rewrite e.
    auto.
Qed.

(* Paths between maps can be converted to homotopies. *)

Definition path_to_homotopy [A] [B : A -> Type]
  (f g : forall x : A, B x) (p : f = g) :
  Homotopy f g :=
  fun x =>
    match p in _ = h return f x = h x with
    | eq_refl _ => eq_refl _
    end.

(* Function extensionality *)

Axiom function_extensionality :
  forall (A : U) (B : A -> U) (f g : forall x : A, B x),
  IsEquiv (path_to_homotopy f g).

(* Paths can be converted to equivalences. *)

Definition path_to_equiv [A B] (p : A = B) :
  { f : A -> B & IsEquiv f } :=
  existT (@IsEquiv A B) (transport p)
    match p with
    | eq_refl => (
        existT (fun g => Homotopy g _) _ (@eq_refl _),
        existT (fun g => Homotopy g _) _ (@eq_refl _)
      )
    end.

(* Univalence *)

Axiom univalence : forall A B : U, IsEquiv (@path_to_equiv A B).

(* Homotopy n-types (starting at 0 rather than the more conventional -2) *)

Fixpoint IsTrunc n (A : Type) :=
  match n with
  | O => { c : A & forall x, c = x }
  | S p => forall x y : A, IsTrunc p (x = y)
  end.

(* Contractible types, a.k.a. homotopy (-2)-types or (-2)-truncated spaces *)

Definition IsContr := IsTrunc 0.

(* Mere propositions, a.k.a. homotopy (-1)-types or (-1)-truncated spaces *)

Definition IsProp := IsTrunc 1.

(* Sets, a.k.a. homotopy 0-types or 0-truncated spaces *)

Definition IsSet := IsTrunc 2.

(* `IsTrunc` defines a filtration on the universe. *)

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

(* An equivalent characterization of being a mere proposition *)

Theorem proof_irrelevance_is_prop A : (forall x y : A, x = y) -> IsProp A.
Proof.
  unfold IsProp, IsTrunc.
  intros.
  exists (H x y).
  destruct x0.
  assert (forall x y (p : x = y), H x y = concat p (H y y)).
  - intros.
    destruct p.
    rewrite left_id.
    reflexivity.
  - specialize (H0 _ _ (H x x)).
    assert (
      forall (x y z : A) (p : x = y) (q r : y = z),
      concat p q = concat p r -> q = r
    ).
    + intros.
      destruct p.
      do 2 rewrite left_id in H1.
      assumption.
    + specialize (H1 _ _ _ (H x x) (H x x) eq_refl).
      auto.
Qed.

(* Being truncated is a mere proposition. *)

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
        destruct (X0 x0 x1 (e x1) (e0 x1)).
        auto.
    + rewrite H.
      reflexivity.
  - destruct (function_extensionality _ _ x y).
    destruct s.
    apply x0.
    unfold Homotopy.
    intro.
    destruct (function_extensionality _ _ (x x1) (y x1)).
    destruct s.
    apply x2.
    unfold Homotopy.
    intro.
    apply IHn.
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
  projT1 (fst (univalence _ _)) (existT _ _ weekend_bit_equiv).

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
  | eq_refl _ => invert_weekend_with_theorem
  end.

Definition invert_bit : Bit -> Bit :=
  proj1_sig invert_bit_with_theorem.

Definition invert_bit_involution : forall x, invert_bit (invert_bit x) = x :=
  proj2_sig invert_bit_with_theorem.

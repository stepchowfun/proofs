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

Definition inv [T : U] [x y : T] (p : x = y) : y = x :=
  match p in _ = z return z = x with
  | eq_refl => eq_refl
  end.

Definition concat [T : U] [x y z : T] (p : x = y) (q : y = z) : x = z :=
  match q in _ = z return x = z with
  | eq_refl => p
  end.

Definition left_id [T : U] [x y : T] (p : x = y) : concat eq_refl p = p :=
  match p return concat eq_refl p = p with
  | eq_refl => eq_refl
  end.

Definition right_id [T : U] [x y : T] (p : x = y) : concat p eq_refl = p :=
  match p return concat p eq_refl = p with
  | eq_refl => eq_refl
  end.

Definition left_inv [T : U] [x y : T] (p : x = y) :
  concat (inv p) p = eq_refl
:=
  match p return concat (inv p) p = eq_refl with
  | eq_refl => eq_refl
  end.

Definition right_inv [T : U] [x y : T] (p : x = y) :
  concat p (inv p) = eq_refl
:=
  match p return concat p (inv p) = eq_refl with
  | eq_refl => eq_refl
  end.

Definition assoc [T : U] [x y z w : T]
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

Definition transport [A] [x y : A] [P : A -> Type] (p : x = y) (px : P x) :=
  match p in _ = z return P z with
  | eq_refl => px
  end.

(* Homotopy *)

Definition Homotopy [X] [Y : X -> Type] (f g : forall x : X, Y x) :=
  forall x, f x = g x.

(* Equivalence *)

Definition IsEquiv [X Y] (f : X -> Y) :=
  { g : Y -> X & Homotopy (f ∘ g) id } *
  { g : Y -> X & Homotopy (g ∘ f) id }.

(* Quasi-inverse *)

Definition QuasiInv [X Y] (f : X -> Y) :=
  { g : Y -> X & Homotopy (f ∘ g) id * Homotopy (g ∘ f) id }.

(* Equivalence is logically equivalent to quasi-inverse. *)

Theorem quasi_inverse_to_equiv :
  forall X Y (f : X -> Y), QuasiInv f -> IsEquiv f.
Proof.
  intros.
  destruct X0, p.
  split; exists x; auto.
Qed.

Theorem equiv_to_quasi_inverse :
  forall X Y (f : X -> Y), IsEquiv f -> QuasiInv f.
Proof.
  unfold IsEquiv, QuasiInv, Homotopy, compose, id.
  intros.
  destruct X0, s, s0.
  exists (fun y => x0 (f (x y))).
  split; intros.
  - rewrite e0.
    auto.
  - rewrite e.
    auto.
Qed.

(* Paths between maps can be converted to homotopies. *)

Definition path_to_homotopy [X] [Y : X -> Type]
  (f g : forall x : X, Y x) (p : f = g) :
  Homotopy f g :=
  fun x =>
    match p in _ = h return f x = h x with
    | eq_refl _ => eq_refl _
    end.

(* Function extensionality *)

Axiom function_extensionality :
  forall (X : U) (Y : X -> U) (f g : forall x : X, Y x),
  IsEquiv (path_to_homotopy f g).

(* Paths can be converted to equivalences. *)

Definition path_to_equiv [X Y] (p : X = Y) :
  { f : X -> Y & IsEquiv f } :=
  existT (@IsEquiv X Y) (transport p)
    match p with
    | eq_refl => (
        existT (fun g => Homotopy g _) _ (@eq_refl _),
        existT (fun g => Homotopy g _) _ (@eq_refl _)
      )
    end.

(* Univalence *)

Axiom univalence : forall (X Y : U), IsEquiv (@path_to_equiv X Y).

(* Homotopy n-types (starting at 0 rather than the more conventional -2) *)

Fixpoint IsTrunc n (X : U) : U :=
  match n with
  | O => { c : X & forall x, c = x }
  | S p => forall x y : X, IsTrunc p (x = y)
  end.

(* Contractible types, a.k.a. homotopy (-2)-types or (-2)-truncated spaces *)

Definition IsContr := IsTrunc 0.

(* Mere propositions, a.k.a. homotopy (-1)-types or (-1)-truncated spaces *)

Definition IsProp := IsTrunc 1.

(* Sets, a.k.a. homotopy 0-types or 0-truncated spaces *)

Definition IsSet := IsTrunc 2.

(* `IsTrunc` defines a filtration on the universe. *)

Theorem is_trunc_cumulative : forall n X, IsTrunc n X -> IsTrunc (1 + n) X.
Proof.
  induction n.
  - unfold IsTrunc.
    cbn.
    intros.
    destruct X0.
    exists (eq_trans (eq_sym (e x)) (e y)).
    intro.
    destruct x1, (e x).
    reflexivity.
  - cbn in *.
    intros.
    apply IHn.
    apply X0.
Qed.

(* An equivalent characterization of being a mere proposition *)

Theorem proof_irrelevance_is_prop X : (forall x y : X, x = y) -> IsProp X.
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
      forall (x y z : X) (p : x = y) (q r : y = z),
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

Theorem is_truncated_is_prop : forall n X, IsProp (IsTrunc n X).
Proof.
  induction n; intros; apply proof_irrelevance_is_prop; intros.
  - unfold IsTrunc in *.
    destruct x, y.
    destruct (e0 x).
    assert (e = e0).
    + assert (IsProp X).
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
        pose proof (is_trunc_cumulative 1 X X0).
        destruct (X1 x0 x1 (e x1) (e0 x1)).
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

Definition weekend_bit_equiv : IsEquiv weekend_to_bit := (
  existT (fun g => Homotopy (weekend_to_bit ∘ g) id)
    bit_to_weekend
    (
      fun x =>
        match x with
        | Zero => eq_refl _
        | One => eq_refl _
        end
    ),
  existT (fun g => Homotopy (g ∘ weekend_to_bit) id)
    bit_to_weekend
    (
      fun x =>
        match x with
        | Saturday => eq_refl _
        | Sunday => eq_refl _
        end
    )
).

Definition weekend_bit_path : Weekend = Bit :=
  projT1
    (fst (univalence Weekend Bit))
    (existT _ weekend_to_bit weekend_bit_equiv).

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
  match weekend_bit_path in _ = Z
  return { invert : Z -> Z | forall x, invert (invert x) = x } with
  | eq_refl _ => invert_weekend_with_theorem
  end.

Definition invert_bit : Bit -> Bit :=
  proj1_sig invert_bit_with_theorem.

Definition invert_bit_involution : forall x, invert_bit (invert_bit x) = x :=
  proj2_sig invert_bit_with_theorem.

(****************************************************************)
(****************************************************************)
(****                                                        ****)
(****   A formalization of the function extensionality and   ****)
(****   univalence axioms                                    ****)
(****                                                        ****)
(****************************************************************)
(****************************************************************)

Require Import Coq.Program.Basics.

#[local] Open Scope program_scope.
#[local] Open Scope type.

(* A universe to be univalent *)

Definition U := Type.

(* Homotopy *)

Definition Homotopy [X] [Y : X -> Type] (f g : forall x : X, Y x) :=
  forall x, f x = g x.

(* Quasi-inverse *)

Definition QuasiInverse [X Y] (f : X -> Y) :=
  { g : Y -> X & Homotopy (f ∘ g) id * Homotopy (g ∘ f) id }.

(* Equivalence *)

Definition Equivalence [X Y] (f : X -> Y) :=
  { g : Y -> X & Homotopy (f ∘ g) id } *
  { g : Y -> X & Homotopy (g ∘ f) id }.

(* Equivalence is logically equivalent to quasi-inverse. *)

Theorem quasi_inverse_to_equivalence :
  forall X Y (f : X -> Y), QuasiInverse f -> Equivalence f.
Proof.
  intros.
  destruct X0, p.
  split; exists x; auto.
Qed.

Theorem equivalence_to_quasi_inverse :
  forall X Y (f : X -> Y), Equivalence f -> QuasiInverse f.
Proof.
  unfold Equivalence, QuasiInverse, Homotopy, compose, id.
  intros.
  destruct X0, s, s0.
  exists (fun y => x0 (f (x y))).
  split; intros.
  - rewrite e0.
    auto.
  - rewrite e.
    auto.
Qed.

(* Equivalence is an equivalence relation. *)

Definition reflexivity X : Equivalence (@id X) := (
  existT (fun g => Homotopy g _) _ (@eq_refl _),
  existT (fun g => Homotopy g _) _ (@eq_refl _)
).

Theorem symmetry [X Y] (f : X -> Y) (e : Equivalence f) :
  { g : Y -> X & Equivalence g }.
Proof.
  assert (QuasiInverse f).
  - apply equivalence_to_quasi_inverse.
    auto.
  - destruct X0.
    exists x.
    apply quasi_inverse_to_equivalence.
    exists f.
    destruct p.
    auto.
Qed.

Theorem transitivity
  [X Y Z] (f : X -> Y) (g : Y -> Z) (e1 : Equivalence f) (e2 : Equivalence g) :
  { h : X -> Z & Equivalence h }.
Proof.
  assert (QuasiInverse f).
  - apply equivalence_to_quasi_inverse.
    auto.
  - assert (QuasiInverse g).
    + apply equivalence_to_quasi_inverse.
      auto.
    + exists (g ∘ f).
      apply quasi_inverse_to_equivalence.
      destruct X0, X1.
      exists (x ∘ x0).
      destruct p, p0.
      unfold Homotopy, compose, id in *.
      split; intro.
      * rewrite h.
        rewrite h1.
        auto.
      * rewrite h2.
        rewrite h0.
        auto.
Qed.

(* Paths can be converted to equivalences. *)

Definition path_to_equivalence [X Y] (p : X = Y) :
  { f : X -> Y & Equivalence f } :=
  match p in _ = Z return { f : X -> Z & Equivalence f } with
  | eq_refl _ => existT _ _ (reflexivity X)
  end.

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
  Equivalence (path_to_homotopy f g).

(* Univalence *)

Axiom univalence : forall (X Y : U), Equivalence (@path_to_equivalence X Y).

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

Definition weekend_bit_equivalence : Equivalence weekend_to_bit := (
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
    (existT _ weekend_to_bit weekend_bit_equivalence).

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

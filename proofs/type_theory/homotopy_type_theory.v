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

(* Equivalence *)

Definition Equivalence [X Y] (f : X -> Y) :=
  { g : Y -> X & Homotopy (f ∘ g) id } *
  { g : Y -> X & Homotopy (g ∘ f) id }.

(* Quasi-inverse *)

Definition QuasiInverse [X Y] (f : X -> Y) :=
  { g : Y -> X & Homotopy (f ∘ g) id * Homotopy (g ∘ f) id }.

(* Equivalence is logically equivalent to quasi-inverse. *)

Theorem quasiInverseToEquivalence :
  forall X Y (f : X -> Y), QuasiInverse f -> Equivalence f.
Proof.
  intros.
  destruct X0, p.
  split; exists x; auto.
Qed.

Theorem equivalenceToQuasiInverse :
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
  - apply equivalenceToQuasiInverse.
    auto.
  - destruct X0.
    exists x.
    apply quasiInverseToEquivalence.
    exists f.
    destruct p.
    auto.
Qed.

Theorem transitivity
  [X Y Z] (f : X -> Y) (g : Y -> Z) (e1 : Equivalence f) (e2 : Equivalence g) :
  { h : X -> Z & Equivalence h }.
Proof.
  assert (QuasiInverse f).
  - apply equivalenceToQuasiInverse.
    auto.
  - assert (QuasiInverse g).
    + apply equivalenceToQuasiInverse.
      auto.
    + exists (g ∘ f).
      apply quasiInverseToEquivalence.
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

Definition pathToEquivalence [X Y] (p : X = Y) :
  { f : X -> Y & Equivalence f } :=
  match p in _ = Z return { f : X -> Z & Equivalence f } with
  | eq_refl _ => existT _ _ (reflexivity X)
  end.

(* Paths between maps can be converted to homotopies. *)

Definition pathToHomotopy [X] [Y : X -> Type]
  (f g : forall x : X, Y x) (p : f = g) :
  Homotopy f g :=
  fun x =>
    match p in _ = h return f x = h x with
    | eq_refl _ => eq_refl _
    end.

(* Function extensionality *)

Axiom function_extensionality :
  forall (X : U) (Y : X -> Type) (f g : forall x : X, Y x),
  Equivalence (pathToHomotopy f g).

(* Univalence *)

Axiom univalence : forall (X Y : U), Equivalence (@pathToEquivalence X Y).

(* An example of using univalence *)

Inductive Bit : U :=
| Zero
| One.

Inductive Weekend : U :=
| Saturday
| Sunday.

Definition weekendToBit x :=
  match x with
  | Saturday => Zero
  | Sunday => One
  end.

Definition bitToWeekend x :=
  match x with
  | Zero => Saturday
  | One => Sunday
  end.

Definition weekendToBitIsEquivalence : Equivalence weekendToBit := (
  existT (fun g => Homotopy (weekendToBit ∘ g) id)
    bitToWeekend
    (
      fun x =>
        match x with
        | Zero => eq_refl _
        | One => eq_refl _
        end
    ),
  existT (fun g => Homotopy (g ∘ weekendToBit) id)
    bitToWeekend
    (
      fun x =>
        match x with
        | Saturday => eq_refl _
        | Sunday => eq_refl _
        end
    )
).

Definition weekendToBitPath : Weekend = Bit :=
  projT1
    (fst (univalence Weekend Bit))
    (existT _ weekendToBit weekendToBitIsEquivalence).

Definition invertWeekend x :=
  match x with
  | Saturday => Sunday
  | Sunday => Saturday
  end.

Theorem invertWeekendInvolution x : invertWeekend (invertWeekend x) = x.
Proof.
  destruct x; auto.
Qed.

Definition invertWeekendWithTheorem :=
  exist (fun invert => forall x, invert (invert x) = x)
    invertWeekend
    invertWeekendInvolution.

Definition invertBitWithTheorem :=
  match weekendToBitPath in _ = Z
  return { invert : Z -> Z | forall x, invert (invert x) = x } with
  | eq_refl _ => invertWeekendWithTheorem
  end.

Definition invertBit : Bit -> Bit :=
  proj1_sig invertBitWithTheorem.

Definition invertBitInvolution : forall x, invertBit (invertBit x) = x :=
  proj2_sig invertBitWithTheorem.

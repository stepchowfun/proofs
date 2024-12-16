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

(* Paths can be converted to equivalences. *)

Definition idIsEquivalence X : Equivalence (@id X) := (
  existT (fun g => Homotopy g _) _ (@eq_refl _),
  existT (fun g => Homotopy g _) _ (@eq_refl _)
).

Definition pathToEquivalence [X Y] (p : X = Y) :
  { f : X -> Y & Equivalence f } :=
  match p in _ = Z return { f : X -> Z & Equivalence f } with
  | eq_refl _ => existT _ _ (idIsEquivalence X)
  end.

(* Paths between functions can be converted to homotopies. *)

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

Definition invertBit : Bit -> Bit :=
  match weekendToBitPath in _ = Z return Z -> Z with
  | eq_refl _ => invertWeekend
  end.

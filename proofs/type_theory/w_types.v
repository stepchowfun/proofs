(***************************************)
(***************************************)
(****                               ****)
(****   An exploration of W types   ****)
(****                               ****)
(***************************************)
(***************************************)

Require Import Coq.Logic.FunctionalExtensionality.

(*
  W-types are the types of well-founded trees and generalize inductive types
  like `bool`, `nat`, `list`, etc. The parameter `A` encodes both the choice of
  constructor and its non-recursive arguments. The family `B` encodes the
  number of recursive arguments for a given choice of `A`. The name `sup` is
  short for "supremum", since each node in the tree is the least upper bound of
  its subtrees in the "subtree of" relation.
*)

Inductive W [A] (B : A -> Type) :=
| sup (a : A) (f : B a -> W B) : W B.

Arguments sup [_ _] _ _.

Check W_ind.

(*
  ```
  W_ind :
    forall (A : Type) (B : A -> Type) (P : W B -> Prop),
    (
      forall (a : A) (f : B a -> W B),
      (forall b : B a, P (f b)) ->
      P (sup a f)
    ) ->
    forall w : W B, P w
  ```
*)

(* The standard encoding of the natural numbers as a W-type is as follows: *)

Definition arities (b : bool) := if b then Empty_set else unit.

Definition PreNat := W arities.

Definition pre_zero : PreNat :=
  sup true (fun x : Empty_set => match x with end).

Definition pre_succ (p : PreNat) : PreNat := sup false (fun _ => p).

Definition pre_recursor P (p_zero : P) (p_succ : P -> P) : PreNat -> P :=
  W_rect bool arities (fun _ => P) (
    fun (a : bool) =>
      match a
      return forall (f : arities a -> W arities) (h : arities a -> P), P
      with
      | true => fun _ _ => p_zero
      | false => fun _ h => p_succ (h tt)
      end
  ).

Definition pre_add m n := pre_recursor PreNat n pre_succ m.

Definition pre_nat_to_standard_nat n := pre_recursor nat 0 S n.

Compute pre_nat_to_standard_nat (
  pre_add (pre_succ pre_zero) (pre_succ (pre_succ pre_zero))
). (* `3` *)

(*
  Unfortunately, we need function extensionality to define the dependent
  eliminator for `PreNat`.
*)

Definition pre_eliminator
  (P : PreNat -> Type)
  (p_zero : P pre_zero)
  (p_succ : forall n, P n -> P (pre_succ n))
: forall n, P n
:=
  W_rect bool arities P (
    fun (a : bool) =>
      match a
      return
        forall (f : arities a -> W arities) (h : forall b, P (f b)),
        P (sup a f)
      with
      | true => fun f _ =>
        match
          functional_extensionality
            (fun x : Empty_set => match x with end)
            f
            (fun x => match x with end)
        in _ = z
        return P (sup true z)
        with
        | eq_refl => p_zero
        end
      | false => fun f h =>
        match
          functional_extensionality
            (fun _ => f tt)
            f
            (
              fun u =>
                match u return f tt = f u with
                | tt => eq_refl (f tt)
                end
            )
        in _ = z
        return P (sup false z)
        with
        | eq_refl => p_succ (f tt) (h tt)
        end
      end
  ).

Goal forall n, pre_add pre_zero n = n.
Proof.
  reflexivity.
Qed.

Goal forall n, pre_add n pre_zero = n.
Proof.
  apply pre_eliminator; auto.
  intros.
  cbn.
  unfold pre_add in H.
  rewrite H.
  reflexivity.
Qed.

(*
  There are two situations above where function extensionality was required:

  1. In the zero case, `f` is not judgmentally equal to
     `fun x : Empty_set => match x with end`, even though they are
     extensionally equal.
  2. In the successor case, `f` is not judgmentally equal to
     `fun _ : unit => f tt`, even though they are extensionally equal. This
     would go through if we had η-conversion for the unit type (along with
     η-conversion on Π types, which we already have in Coq).

  This encoding of natural numbers suffers from the general issue that the `f`
  argument of the `sup` constructor interacts poorly with judgmental equality
  by virtue of being a function. For example, here's another definition of zero
  that is extensionally but not judgmentally equal to `zero`:
*)

Definition other_zero : PreNat := sup true (fun _ : Empty_set => pre_zero).

Goal pre_zero = other_zero.
Proof.
  assert_fails reflexivity. (* Not judgmentally equal *)
  unfold pre_zero, other_zero.
  f_equal.
  apply functional_extensionality.
  intro.
  destruct x.
Qed.

(*
  There's a more sophisticated encoding of natural numbers as a W-type which
  doesn't require function extensionality to define a dependent eliminator, as
  long as we have η-conversion for Π and Σ types. It's described in the
  following paper:

    Jasper Hugunin. Why Not W?. In 26th International Conference on Types for
    Proofs and Programs (TYPES 2020). Leibniz International Proceedings in
    Informatics (LIPIcs), Volume 188, pp. 8:1-8:9, Schloss Dagstuhl –
    Leibniz-Zentrum für Informatik (2021)
    https://doi.org/10.4230/LIPIcs.TYPES.2020.8

  The Σ type in Coq's standard library doesn't have definitional
  η-conversion:
*)

Goal
  forall T (P : T -> Type) (s : { x : T & P x }),
  s = existT _ (projT1 s) (projT2 s).
Proof.
  intros.
  assert_fails reflexivity. (* Conversion fails. *)
  destruct s.
  reflexivity.
Qed.

(*
  However, we can define a Σ with η-conversion as a primitive record type:
*)

Record Sigma [T] (P : T -> Type) := sigma { x : T; y : P x }.

Arguments sigma [_] _ _ _.
Arguments x [_ _] _.
Arguments y [_ _] _.

Goal
  forall T (P : T -> Type) (s : Sigma P),
  s = {| x := s.(x); y := s.(y) |}.
Proof.
  intros.
  reflexivity. (* Conversion succeeds. *)
Qed.

(* Now we can proceed to define `Nat`. *)

Fixpoint Canonical (n : PreNat) : Type :=
  match n with
  | sup true f => (fun x : Empty_set => match x with end) = f
  | sup false f =>
    Sigma (fun k => Sigma (fun _ : (fun _ => k) = f => Canonical (f tt)))
  end.

Definition Nat := Sigma Canonical.

Definition zero : Nat := {|
  x := sup true (fun x : Empty_set => match x with end);
  y := eq_refl;
|}.

Definition succ (n : Nat) : Nat := {|
  x := sup false (fun _ => n.(x));
  y := {| x := _; y := {| x := eq_refl; y := n.(y) |} |}
|}.

Definition eliminator
  (P : Nat -> Type)
  (p_zero : P zero)
  (p_succ : forall n, P n -> P (succ n))
  (n : Nat)
: P n
:=
  let H n := forall c : Canonical n, P {| x := n; y := c |} in
  W_rect bool arities H
  (
    fun (a : bool) =>
      match a
      return
        forall (f : arities a -> W arities) (h : forall b, H (f b)),
        H (sup a f)
      with
      | true => fun f _ c =>
        match c in _ = z return P {| x := sup true z; y := c |} with
        | eq_refl => p_zero
        end
      | false => fun f h c =>
        let eq := c.(y).(x) in
        match eq
        in _ = z
        return
          forall p : Canonical (z tt),
          P {| x := z tt; y := p |} ->
          P {|
            x := sup false z;
            y := {| x := c.(x); y := {| x := eq; y := p |} |}
          |}
        with
        | eq_refl => fun p ih => p_succ {| x := c.(x); y := p |} ih
        end
        c.(y).(y) (h tt c.(y).(y))
      end
  ) n.(x) n.(y).

Definition recursor P (p_zero : P) (p_succ : P -> P) (n : Nat) : P :=
  eliminator (fun _ => P) p_zero (fun _ x => p_succ x) n.

Definition add m n := recursor Nat n succ m.

Definition nat_to_standard_nat n := recursor nat 0 S n.

Compute nat_to_standard_nat (add (succ zero) (succ (succ zero))). (* `3` *)

Goal forall n, add zero n = n.
Proof.
  reflexivity.
Qed.

Goal forall n, add n zero = n.
Proof.
  apply eliminator; auto.
  intros.
  change (succ (recursor Nat zero succ n) = succ n).
  unfold add in H.
  rewrite H.
  reflexivity.
Qed.

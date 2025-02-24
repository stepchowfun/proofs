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
  constructor and its non- recursive arguments. The family `B` encodes the
  number of recursive arguments for a given choice of `A`. The name `sup` is
  short for "supremum", since each node in the tree is the least upper bound of
  its subtrees in the "subtree of" relation.
*)

Inductive W [A : Type] (B : A -> Type) :=
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

Definition Nat := W arities.

Definition zero : Nat := sup true (fun x : Empty_set => match x with end).

Definition succ (p : Nat) : Nat := sup false (fun _ => p).

Definition recursor (P : Type) (p_zero : P) (p_succ : P -> P) : Nat -> P :=
  W_rect bool arities (fun _ => P) (
    fun (a : bool) =>
      match a
      return forall (f : arities a -> W arities) (h : arities a -> P), P
      with
      | true => fun f h => p_zero
      | false => fun f h => p_succ (h tt)
      end
  ).

Definition add m n := recursor Nat n succ m.

Definition toBuiltInNat n := recursor nat 0 S n.

Compute toBuiltInNat (add (succ zero) (succ (succ zero))). (* `3` *)

(*
  Unfotunately, to defined the dependent eliminator for this encoding of `Nat`,
  we need function extensionality.
*)

Definition eliminator
  (P : Nat -> Type)
  (p_zero : P zero)
  (p_succ : forall n, P n -> P (succ n))
: forall n, P n
:=
  W_rect bool arities P (
    fun (a : bool) =>
      match a
      return
        forall (f : arities a -> W arities) (h : forall b, P (f b)),
        P (sup a f)
      with
      | true => fun f h =>
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

(*
  There are two situations above where function extensionality was required:

  1. In the zero case, `f` is not judgmentally equal to
     `fun x : Empty_set => match x with end`, even though they are
     extensionally equal.
  2. In the successor case, `f` is not judgmentally equal to
     `fun _ : unit => f tt`, even though they are extensionally equal.

  There's a more sophisticated encoding of natural numbers as a W-type which
  doesn't require function extensionality to define a dependent eliminator.
  It's described in the following paper:

    Jasper Hugunin. Why Not W?. In 26th International Conference on Types for
    Proofs and Programs (TYPES 2020). Leibniz International Proceedings in
    Informatics (LIPIcs), Volume 188, pp. 8:1-8:9, Schloss Dagstuhl –
    Leibniz-Zentrum für Informatik (2021)
    https://doi.org/10.4230/LIPIcs.TYPES.2020.8
*)

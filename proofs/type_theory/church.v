(*****************************************************************************)
(*****************************************************************************)
(****                                                                     ****)
(****   A demonstration (but not a proof) of why Church encodings don't   ****)
(****   support dependent elimination                                     ****)
(****                                                                     ****)
(*****************************************************************************)
(*****************************************************************************)

(*
  This file demonstrates the problems one encounters when trying to implement
  inductive types (in particular, pairs) with Church encodings. For an actual
  impossibility result, see:

    Geuvers, H. (2001). Induction Is Not Derivable in Second Order Dependent
    Type Theory. In: Abramsky, S. (eds) Typed Lambda Calculi and Applications.
    TLCA 2001. Lecture Notes in Computer Science, vol 2044. Springer, Berlin,
    Heidelberg. https://doi.org/10.1007/3-540-45413-6_16

  These encodings of pairs require an impredicative universe in order to be
  defined in the same universe as their component types, so we'll use `Prop`.
*)

Module NonDependentPairsWithNonDependentElimination.
  (*
    Just as in System F, non-dependent pairs with non-dependent elimination
    work fine, but we don't get eta equivalence.
  *)

  Definition Pair (X Y : Prop) : Prop :=
    forall (Z : Prop), (X -> Y -> Z) -> Z.

  Definition construct (X Y : Prop) : X -> Y -> Pair X Y :=
    fun x y Z f => f x y.

  Definition eliminate (X Y Z : Prop) : (X -> Y -> Z) -> Pair X Y -> Z :=
    fun f p => p Z f.

  Definition first (X Y : Prop) : Pair X Y -> X :=
    fun p => eliminate X Y X (fun x _ => x) p.

  Definition second (X Y : Prop) : Pair X Y -> Y :=
    fun p => eliminate X Y Y (fun _ y => y) p.

  Theorem beta_first :
    forall (X Y : Prop) (x : X) (y : Y), first X Y (construct X Y x y) = x.
  Proof.
    reflexivity.
  Qed.

  Theorem beta_second :
    forall (X Y : Prop) (x : X) (y : Y), second X Y (construct X Y x y) = y.
  Proof.
    reflexivity.
  Qed.

  Axiom eta :
    forall (X Y : Prop) (p : Pair X Y),
    construct X Y (first X Y p) (second X Y p) = p.
End NonDependentPairsWithNonDependentElimination.

Module DependentPairsWithNonDependentElimination.
  (*
    Dependent pairs with non-dependent elimination almost work, except we can't
    define the second projection in full generality. In other words, we can
    encode "weak sums" (i.e., existentials) but not "strong sums". Of course,
    without the second projection, we don't have the associated equivalences.
  *)

  Definition Pair (X : Prop) (Y : X -> Prop) : Prop :=
    forall (Z : Prop), (forall x, Y x -> Z) -> Z.

  Definition construct (X : Prop) (Y : X -> Prop) :
    forall (x : X), Y x -> Pair X Y
  :=
    fun x y Z f => f x y.

  Definition eliminate (X : Prop) (Y : X -> Prop) (Z : Prop) :
    (forall (x : X), Y x -> Z) -> Pair X Y -> Z
  :=
    fun f p => p Z f.

  Definition first (X : Prop) (Y : X -> Prop) : Pair X Y -> X :=
    fun p => eliminate X Y X (fun x _ => x) p.

  (*
    ```
    Definition second (X : Prop) (Y : X -> Prop) (p : Pair X Y) :
      Y (first X Y p)
    :=
      eliminate X Y (Y (first X Y p)) (fun _ y => y) p.
    ```
  *)

  Parameter second :
    forall (X : Prop) (Y : X -> Prop) (p : Pair X Y), Y (first X Y p).

  Theorem beta_first :
    forall (X : Prop) (Y : X -> Prop) (x : X) (y : Y x),
    first X Y (construct X Y x y) = x.
  Proof.
    reflexivity.
  Qed.

  Axiom beta_second :
    forall (X : Prop) (Y : X -> Prop) (x : X) (y : Y x),
    second X Y (construct X Y x y) = y.

  Axiom eta :
    forall (X : Prop) (Y : X -> Prop) (p : Pair X Y),
    construct X Y (first X Y p) (second X Y p) = p.
End DependentPairsWithNonDependentElimination.

Module NonDependentPairsWithDependentElimination.
  (*
    We can't even define the type former for non-dependent pairs with dependent
    elimination. In other words, we don't have an encoding of pairs with an
    induction principle.
  *)

  (*
    ```
    Definition Pair (X Y : Prop) : Prop :=
      forall (Z : Pair X Y -> Prop),
      (forall (x : X) (y : Y), Z (construct X Y x y)) ->
      forall (p : Pair X Y), Z p.
    ```
  *)
End NonDependentPairsWithDependentElimination.

Module DependentPairsWithDependentElimination.
  (*
    Dependent pairs with dependent elimination (i.e., sigma types) have the
    same problem.
  *)

  (*
    ```
    Definition Pair (X : Prop) (Y : X -> Prop) : Prop :=
      forall (Z : Pair X Y -> Prop),
      (forall (x : X) (y : Y x), Z (construct X Y x y)) ->
      forall (p : Pair X Y), Z p.
    ```
  *)
End DependentPairsWithDependentElimination.

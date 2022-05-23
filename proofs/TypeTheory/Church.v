(*****************************************************************************)
(*****************************************************************************)
(****                                                                     ****)
(****   A demonstration of why Church encodings don't support dependent   ****)
(****   elimination                                                       ****)
(****                                                                     ****)
(*****************************************************************************)
(*****************************************************************************)

Module NonDependentPairsWithNonDependentElimination.
  (*
    Non-dependent pairs with non-dependent elimination work fine, just as they
    do in System F.
  *)

  Definition Pair (X Y : Type) : Type :=
    forall Z, (X -> Y -> Z) -> Z.

  Definition construct (X Y : Type) : X -> Y -> Pair X Y :=
    fun x y Z f => f x y.

  Definition eliminate (X Y Z : Type) : (X -> Y -> Z) -> Pair X Y -> Z :=
    fun f p => p Z f.

  Definition first (X Y : Type) : Pair X Y -> X :=
    fun p => eliminate X Y X (fun x _ => x) p.

  Definition second (X Y : Type) : Pair X Y -> Y :=
    fun p => eliminate X Y Y (fun _ y => y) p.

  Compute first bool nat (construct bool nat true 42).
  Compute second bool nat (construct bool nat true 42).
End NonDependentPairsWithNonDependentElimination.

Module DependentPairsWithNonDependentElimination.
  (*
    Dependent pairs with non-dependent elimination almost work, except we can't
    define the second projection in full generality. In other words, we can
    encode "weak existentials" but not "strong existentials".
  *)

  Definition Pair (X : Type) (Y : X -> Type) : Type :=
    forall (Z : Type), (forall x, Y x -> Z) -> Z.

  Definition construct (X : Type) (Y : X -> Type) :
    forall (x : X), Y x -> Pair X Y
  :=
    fun x y Z f => f x y.

  Definition eliminate (X : Type) (Y : X -> Type) (Z : Type) :
    (forall (x : X), Y x -> Z) -> Pair X Y -> Z
  :=
    fun f p => p Z f.

  Definition first (X : Type) (Y : X -> Type) : Pair X Y -> X :=
    fun p => eliminate X Y X (fun x _ => x) p.

  (*
    Definition second (X : Type) (Y : X -> Type) (p : Pair X Y) :
      Y (first X Y p)
  :=
    eliminate X Y (Y (first X Y p)) (fun _ y => y) p.
  *)

  Definition nonDependentSecond (X : Type) (Y : Type) :
    Pair X (fun _ => Y) -> Y
  :=
    fun p => eliminate X (fun _ => Y) Y (fun _ y => y) p.

  Compute first bool (fun _ => nat) (construct bool (fun _ => nat) true 42).
  Compute nonDependentSecond bool nat (construct bool (fun _ => nat) true 42).
End DependentPairsWithNonDependentElimination.

Module NonDependentPairsWithDependentElimination.
  (*
    We can't even define the type former for non-dependent pairs with dependent
    elimination. In other words, we don't have an encoding of pairs with an
    induction principle.
  *)

  (*
    Definition Pair (X Y : Type) : Type :=
      forall (Z : Pair X Y -> Type),
      (forall (x : X) (y : Y), Z (construct X Y x y)) ->
      Z ?.
  *)
End NonDependentPairsWithDependentElimination.

Module DependentPairsWithDependentElimination.
  (*
    Dependent pairs with dependent elimination (i.e., sigma types) have the
    same problem.
  *)

  (*
    Definition Pair (X : Type) (Y : X -> Type) : Type :=
      forall (Z : Pair X Y -> Type),
      (forall (x : X) (y : Y x), Z (construct X Y x y)) ->
      Z ?.
  *)
End DependentPairsWithDependentElimination.

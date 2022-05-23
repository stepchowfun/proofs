(*****************************************************************************)
(*****************************************************************************)
(****                                                                     ****)
(****   A demonstration of why Church encodings don't support dependent   ****)
(****   elimination                                                       ****)
(****                                                                     ****)
(*****************************************************************************)
(*****************************************************************************)

(* These encodings require an impredicative universe, so we will use Prop. *)

Inductive A : Prop :=
| foo : A
| bar : A.

Inductive B : Prop :=
| baz : B
| qux : B.

Module NonDependentPairsWithNonDependentElimination.
  (*
    Non-dependent pairs with non-dependent elimination work fine, just as they
    do in System F.
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

  Compute first A B (construct A B bar qux).
  Compute second A B (construct A B bar qux).
End NonDependentPairsWithNonDependentElimination.

Module DependentPairsWithNonDependentElimination.
  (*
    Dependent pairs with non-dependent elimination almost work, except we can't
    define the second projection in full generality. In other words, we can
    encode "weak existentials" but not "strong existentials".
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
    Definition second (X : Prop) (Y : X -> Prop) (p : Pair X Y) :
      Y (first X Y p)
  :=
    eliminate X Y (Y (first X Y p)) (fun _ y => y) p.
  *)

  Definition nonDependentSecond (X : Prop) (Y : Prop) :
    Pair X (fun _ => Y) -> Y
  :=
    fun p => eliminate X (fun _ => Y) Y (fun _ y => y) p.

  Compute first A (fun _ => B) (construct A (fun _ => B) bar qux).
  Compute nonDependentSecond A B (construct A (fun _ => B) bar qux).
End DependentPairsWithNonDependentElimination.

Module NonDependentPairsWithDependentElimination.
  (*
    We can't even define the type former for non-dependent pairs with dependent
    elimination. In other words, we don't have an encoding of pairs with an
    induction principle.
  *)

  (*
    Definition Pair (X Y : Prop) : Prop :=
      forall (Z : Pair X Y -> Prop),
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
    Definition Pair (X : Prop) (Y : X -> Prop) : Prop :=
      forall (Z : Pair X Y -> Prop),
      (forall (x : X) (y : Y x), Z (construct X Y x y)) ->
      Z ?.
  *)
End DependentPairsWithDependentElimination.

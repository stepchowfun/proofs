(****************************************************************)
(****************************************************************)
(****                                                        ****)
(****   The data needed for the Kleene fixed-point theorem   ****)
(****                                                        ****)
(****************************************************************)
(****************************************************************)

Module Type KleeneData.
  (*
    Assumption: Let (`T`, `Leq`) be a partially ordered set, or poset. A poset
    is a set with a binary relation that is reflexive, transitive, and
    antisymmetric.
  *)

  Parameter T : Type.
  Parameter Leq : T -> T -> Prop.

  Axiom reflexivity : forall x, Leq x x.
  Axiom transitivity : forall x y z, Leq x y -> Leq y z -> Leq x z.
  Axiom antisymmetry : forall x y, Leq x y -> Leq y x -> x = y.

  Hint Resolve reflexivity : main.
  Hint Resolve transitivity : main.
  Hint Resolve antisymmetry: main.
  Hint Rewrite antisymmetry: main.

  (*
    A supremum of a subset of `T` is a least element of `T` which is greater
    than or equal to every element in the subset. This is also called a join or
    least upper bound.
  *)

  Definition Supremum P x1 :=
    (forall x2, P x2 -> Leq x2 x1) /\
    forall x3, (forall x2, P x2 -> Leq x2 x3) -> Leq x1 x3.

  Hint Unfold Supremum : main.

  (*
    A directed subset of `T` is a non-empty subset of `T` such that any two
    elements in the subset have an upper bound in the subset.
  *)

  Definition Directed P :=
    (exists x1, P x1) /\
    forall x1 x2, P x1 -> P x2 -> exists x3, Leq x1 x3 /\ Leq x2 x3 /\ P x3.

  Hint Unfold Directed : main.

  (*
    Assumption: Let the partial order be directed-complete. That means every
    directed subset has a supremum.
  *)

  Axiom directed_complete :
    forall P,
    Directed P ->
    exists x, Supremum P x.

  Hint Resolve directed_complete : main.

  (*
    Assumption: Let `T` have a least element called bottom. This makes our
    partial order a pointed directed-complete partial order.
  *)

  Parameter bottom : T.

  Axiom bottom_least : forall x, Leq bottom x.

  Hint Resolve bottom_least : main.
End KleeneData.

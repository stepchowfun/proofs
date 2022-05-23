(****************************************************************)
(****************************************************************)
(****                                                        ****)
(****   The data needed for the Kleene fixed-point theorem   ****)
(****                                                        ****)
(****************************************************************)
(****************************************************************)

Module Type KleeneData.
  (*
    Assumption: Let (`T`, `leq`) be a partially ordered set, or poset. A poset
    is a set with a binary relation that is reflexive, transitive, and
    antisymmetric.
  *)

  Parameter T : Type.
  Parameter leq : T -> T -> Prop.

  Axiom reflexivity : forall x, leq x x.
  Axiom transitivity : forall x y z, leq x y -> leq y z -> leq x z.
  Axiom antisymmetry : forall x y, leq x y -> leq y x -> x = y.

  #[export] Hint Resolve reflexivity : main.
  #[export] Hint Resolve transitivity : main.
  #[export] Hint Resolve antisymmetry: main.
  #[export] Hint Rewrite antisymmetry: main.

  (*
    A supremum of a subset of `T` is a least element of `T` which is greater
    than or equal to every element in the subset. This is also called a join or
    least upper bound.
  *)

  Definition supremum P x1 :=
    (forall x2, P x2 -> leq x2 x1) /\
    forall x3, (forall x2, P x2 -> leq x2 x3) -> leq x1 x3.

  #[export] Hint Unfold supremum : main.

  (*
    A directed subset of `T` is a non-empty subset of `T` such that any two
    elements in the subset have an upper bound in the subset.
  *)

  Definition directed P :=
    (exists x1, P x1) /\
    forall x1 x2, P x1 -> P x2 -> exists x3, leq x1 x3 /\ leq x2 x3 /\ P x3.

  #[export] Hint Unfold directed : main.

  (*
    Assumption: Let the partial order be directed-complete. That means every
    directed subset has a supremum.
  *)

  Axiom directedComplete :
    forall P,
    directed P ->
    exists x, supremum P x.

  #[export] Hint Resolve directedComplete : main.

  (*
    Assumption: Let `T` have a least element called bottom. This makes our
    partial order a pointed directed-complete partial order.
  *)

  Parameter bottom : T.

  Axiom bottomLeast : forall x, leq bottom x.

  #[export] Hint Resolve bottomLeast : main.
End KleeneData.

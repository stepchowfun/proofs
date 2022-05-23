(***************************************************************************)
(***************************************************************************)
(****                                                                   ****)
(****   Restrictions imposed by Coq to ensure all functions terminate   ****)
(****                                                                   ****)
(***************************************************************************)
(***************************************************************************)

(********************************************************)
(* All functions must be statically known to terminate. *)
(********************************************************)

(*
  Fixpoint f (n : nat) : nat := f n.
*)

(***************************************************)
(* A brief summary of the universe behavior in Coq *)
(***************************************************)

(*
  We have an infinite heirarchy of predicative universes Type_i for all i >= 0.
  Universes are cummulative, so x : Type_i implies x : Type_(i+1). Type_0 is
  called Set. Parallel to Set, we also have an impredicative universe called
  Prop : Type_1.
*)

(* If B : Prop, then A -> B : Prop. *)

Check Set -> True. (* Prop *)

(* Otherwise, if A, B : Type_i, then A -> B : Type_i. *)

Check Set -> nat. (* Type@{Set+1} *)

(* Here are some identity functions for different universes: *)

Definition idProp (t : Prop) (x : t) := x.
Definition idSet  (t : Set) (x : t) := x.

(* Because Prop is impredicative, we can apply idProp to itself. *)

Check idProp (forall t : Prop, t -> t) idProp. (* forall t : Prop, t -> t *)

(*
  But Set (a.k.a. Type_0) is predicative, so we can't apply idSet to itself:

  Check idSet (forall t : Set, t -> t) idSet.
*)

(*
  For any i, Type_i is predicative. Let's fix some particular universe level i.
*)

Definition universe := Type.

(* Here's an identity function for that universe: *)

Definition idUniverse (t : universe) (x : t) := x.

(*
  Like with idSet, predicativity forbids the following:

  Check idUniverse (forall t : universe, t -> t) idUniverse.
*)

(*****************************************************************************)
(* Inductive types have a "strict positivity requirement" to prevent Curry's *)
(* paradox.                                                                  *)
(*****************************************************************************)

(*
  The following is not allowed:

  Inductive bad :=
  | makeBad : (bad -> bool) -> bad.

  Suppose bad were allowed. Consider the following function:

  Definition evil (x : bad) : bool :=
    match x with
    | makeBad f => f x
    end.

  We could use evil to construct the following diverging term:

  Definition catastrophe : bool := evil (makeBad evil).

  Note that this is also rejected:

  Inductive alsoBad :=
  | makeAlsoBad : ((alsoBad -> bool) -> bool) -> alsoBad.

  alsoBad can be used to construct a diverging function in an impredicative
  universe, as demonstrated in this paper:

  Coquand, T., Paulin, C. (1990). Inductively defined types. In: Martin-Löf,
  P., Mints, G. (eds) COLOG-88. COLOG 1988. Lecture Notes in Computer Science,
  vol 417. Springer, Berlin, Heidelberg.
  https://doi.org/10.1007/3-540-52335-9_47
*)

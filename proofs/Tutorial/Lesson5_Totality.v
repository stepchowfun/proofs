(***************************************************************************)
(***************************************************************************)
(****                                                                   ****)
(****   Restrictions imposed by Coq to ensure all functions terminate   ****)
(****                                                                   ****)
(***************************************************************************)
(***************************************************************************)

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

(********************************************************)
(* All functions must be statically known to terminate. *)
(********************************************************)

(*
  Fixpoint f (n : nat) : nat := f n.
*)

(***********************************************************)
(* Inductive types have a "strict positivity requirement". *)
(***********************************************************)

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
*)

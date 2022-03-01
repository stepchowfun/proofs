(*******************************)
(*******************************)
(****                       ****)
(****   Coq's type theory   ****)
(****                       ****)
(*******************************)
(*******************************)

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
Definition idSet  (t : Set ) (x : t) := x.

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

(***********************************************************)
(* A demonstration that inductive families (not to be      *)
(* confused with families of inductive types) and          *)
(* propositional equality can be encoded in terms of each  *)
(* other.                                                  *)
(***********************************************************)

Inductive Exp : Set -> Type :=
| Zero : Exp nat
| Succ : Exp nat -> Exp nat
| Pair : forall b c, Exp b -> Exp c -> Exp (prod b c).

Fixpoint eval (a : Set) (e1 : Exp a) : a :=
  match e1 in Exp b return b with
  | Zero => 0
  | Succ e2 => eval nat e2 + 1
  | Pair c d e2 e3 => (eval c e2, eval d e3)
  end.

Inductive Exp2 (a : Set) : Type :=
| Zero2 : nat = a -> Exp2 a
| Succ2 : nat = a -> Exp2 a -> Exp2 a
| Pair2 : forall (b c : Set), (prod b c) = a -> Exp2 b -> Exp2 c -> Exp2 a.

Fixpoint eval2 (a : Set) (e1 : Exp2 a) : a :=
  match e1 with
  | Zero2 _ H => match H in (_ = b) return b with
                 | eq_refl => 0
                 end
  | Succ2 _ H e2 => match H in (_ = b) return b with
                    | eq_refl => eval2 nat (
                                   match (eq_sym H)
                                   in (_ = c)
                                   return Exp2 c with
                                   | eq_refl => e2
                                   end
                                 ) + 1
                    end
  | Pair2 _ b c H e2 e3 => match H in (_ = b) return b with
                           | eq_refl => (eval2 b e2, eval2 c e3)
                           end
  end.

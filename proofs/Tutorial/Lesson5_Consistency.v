(****************************************************************************)
(****************************************************************************)
(****                                                                    ****)
(****   Restrictions imposed by Coq to ensure consistency of the logic   ****)
(****                                                                    ****)
(****************************************************************************)
(****************************************************************************)

(********************************************************)
(* All functions must be statically known to terminate. *)
(********************************************************)

(*
  If we were allowed to write nonterminating functions, we could prove `False`.

  ```
  Fixpoint f (n : nat) : False := f n.

  Definition paradox : False := f 0.
  ```

  To prevent this, Coq requires that recursive functions have some argument
  which is structurally "decreasing" at every recursive call. Coq can
  automatically figure out which argument that is.
*)

(***************************************************)
(* A brief summary of the universe behavior in Coq *)
(***************************************************)

(*
  Consider a type, such as `nat`. What is its type? Suppose we call it `Type`,
  so `nat : Type`. Then what is the type of `Type`?

  One might guess that `Type` is its own type, i.e., `Type : Type`. However, in
  a rather convoluted way, this would allow one to define a nonterminating
  function and prove `False`. This is called Girard's paradox, and you can find
  it in this repo here:

    https://github.com/stepchowfun/proofs/blob/main/proofs/TypeTheory/Girard.v

  So, instead of having `Type : Type`, we have an infinite heirarchy of
  universes `Type_i` for all `i` >= 0. For convenience, universes are
  cummulative, so `x : Type_i` implies `x : Type_(i+1)`. `Type_0` is called
  `Set`. All of these `Type_i` universes, including `Set`, are "predicative",
  which will be explained below. However, in the same universe as `Set`
  (namely, `Type_1`), we also have an "impredicative" universe called `Prop`.
*)

(*
  If `A, B : Type_i`, then `A -> B : Type_i`. This is called *predicativity*.
*)

Check bool -> nat. (* `Set` *)
Check Set -> Set. (* `Type@{Set+1}` *)
Check Prop -> Set. (* `Type@{Set+1}` *)

(*
  If `A` and `B` are in different universes, there will be some higher universe
  which contains them both due to cummulativity.
*)

Check Set -> nat. (* `Type@{Set+1}` *)

(* If `B : Prop`, then `A -> B : Prop`. This is called *impredicativity*. *)

Check nat -> True. (* `Prop` *)
Check Set -> True. (* `Prop` *)
Check Prop -> True. (* `Prop` *)

(* Here are some identity functions for different universes: *)

Definition idProp (t : Prop) (x : t) := x.
Definition idSet  (t : Set) (x : t) := x.

(* Because `Prop` is impredicative, we can apply `idProp` to itself. *)

Check idProp (forall t : Prop, t -> t) idProp. (* `forall t : Prop, t -> t` *)

(*
  But `Set` (a.k.a. `Type_0`) is predicative, so we can't apply `idSet` to
  itself:

  ```
  Check idSet (forall t : Set, t -> t) idSet.
  ```
*)

(*
  When we write `Type`, Coq automatically figures out which level `i` should be
  used. In fact, there is no way to explicitly specify it.

  Let's fix some particular universe and let Coq choose some level `i` for it.
*)

Definition universe := Type.

(* Here's an identity function for that universe: *)

Definition idUniverse (t : universe) (x : t) := x.

(*
  Like with `idSet`, predicativity forbids the following:

  ```
  Check idUniverse (forall t : universe, t -> t) idUniverse.
  ```
*)

(*************************************************)
(* Information cannot leave the `Prop` universe. *)
(*************************************************)

(*
  Everything in `Prop` is considered a proposition, and the inhabitants of
  those propositions are considered proofs. For example, the following
  proposition has two proofs:
*)

Inductive myProp : Prop :=
| proof1 : myProp
| proof2 : myProp.

(* Since `myProp` is an inductive type, it supports pattern matching. *)

Definition flipFlop (proof : myProp) : myProp :=
  match proof with
  | proof1 => proof2
  | proof2 => proof1
  end.

(*
  As we will see in the next lesson, Coq code can be "extracted" into code in
  other languages such that the proofs are erased. But in order for extraction
  to be make sense, it's important that none of the extracted code makes
  decisions based on the erased proofs. Coq guarantees this with a restriction
  on pattern matching. The following is rejected because the return type is not
  in `Prop`:

  ```
  Definition myPropToNat (proof : myProp) : nat :=
    match proof with
    | proof1 => 0
    | proof2 => 1
    end.
  ```

  However, if a proposition has zero constructors or one constructor for which
  the non-parameter arguments are proofs, then pattern matching on it doesn't
  result in any decisions being made based on the proof. Thus, Coq allows the
  following:
*)

Definition falseToNat (proof : False) : nat :=
  match proof with
  end.

Definition trueToNat (proof : True) : nat :=
  match proof with
  | I => 0
  end.

Definition falseAndTrueToNat (proof : False /\ True) : nat :=
  match proof with
  | conj _ _ => 0
  end.

Definition eqToNat (proof : false = false) : nat :=
  match proof with
  | eq_refl _ => 0
  end.

(***********************************************************)
(* Inductive types have a "strict positivity requirement". *)
(***********************************************************)

(* The following `weird` type is allowed, even though it has no inhabitants. *)

Inductive weird :=
| makeWeird : weird -> weird.

(*
  However, the following is not allowed:

  ```
  Inductive bad :=
  | makeBad : (bad -> nat) -> bad.
  ```

  Why not? Suppose `bad` were allowed. Consider the following function:

  ```
  Definition evil (x : bad) : nat :=
    match x with
    | makeBad f => f x
    end.
  ```

  We could use `evil` to construct the following diverging term:

  ```
  Definition catastrophe : nat := evil (makeBad evil).
  ```

  This is also rejected:

  ```
  Inductive alsoBad :=
  | makeAlsoBad : ((alsoBad -> nat) -> nat) -> alsoBad.
  ```

  `alsoBad` can be used to construct a diverging function in an impredicative
  universe, as demonstrated in this paper:

    Coquand, T., Paulin, C. (1990). Inductively defined types. In: Martin-Löf,
    P., Mints, G. (eds) COLOG-88. COLOG 1988. Lecture Notes in Computer
    Science, vol 417. Springer, Berlin, Heidelberg.
    https://doi.org/10.1007/3-540-52335-9_47

  `alsoBad` is not known to cause any theoretical issues in predicative
  universes, but Coq still rejects it regardless of the universe in which it's
  defined.
*)

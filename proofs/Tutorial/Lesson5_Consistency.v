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

(*********************************)
(* Universes and inductive types *)
(*********************************)

(* Let's define a universe larger than `Set`. *)

Definition large := Type.

Definition constraint : large := Set.

(*
  An inductive type must either live in `Prop` or in a higher universe than the
  universes of the arguments to its constructors, including indices but not
  parameters.
*)

Inductive foo1 : Set :=
| makeFoo1 : forall (x : nat), foo1.

(*
  Inductive foo2 : Set :=
  | makeFoo2 : forall (x : Set), foo2.

  Inductive foo3 : Set -> Set :=
  | makeFoo3 : forall (x : Set), foo3 x.
*)

Inductive foo3 : Prop :=
| makeFoo3 : forall (x : Set), foo3.

Inductive foo4 : Set -> Prop :=
| makeFoo4 : forall (x : Set), foo4 x.

Inductive foo5 : Prop :=
| makeFoo5 : forall (x : large), foo5.

Inductive foo6 : large -> Prop :=
| makeFoo6 : forall (x : large), foo6 x.

(*
  There's no constraint between the universe of an inductive type and the
  universes of its parameters.
*)

Inductive foo7 (x : Set) : Set :=
| makeFoo7 : foo7 x.

Inductive foo8 (x : large) : Set :=
| makeFoo8 : foo8 x.

(***********************************************************)
(* Inductive types have a "strict positivity requirement". *)
(***********************************************************)

(* The following type is allowed, even though it has no inhabitants. *)

Inductive weird :=
| makeWeird : weird -> weird.

(* This "reflexive" type is also allowed: *)

Inductive weirder :=
| makeWeirder : (nat -> weirder) -> weirder.

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

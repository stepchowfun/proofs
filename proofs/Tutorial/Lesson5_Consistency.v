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

(* Coq rejects all nonterminating functions: *)

Fail Fixpoint f (n : nat) : False := f n.

(*
  ```
  The command has indeed failed with message:
  Recursive definition of f is ill-formed.
  In environment
  f : nat -> False
  n : nat
  Recursive call to f has principal argument equal to
  "n" instead of a subterm of "n".
  Recursive definition is: "fun n : nat => f n".
  ```

  If we were allowed to write that function, we could use it to prove `False`:

  ```
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
  cumulative, so `x : Type_i` implies `x : Type_{i+1}`. `Type_0` is called
  `Set`. All of these `Type_i` universes, including `Set`, are "predicative",
  which will be explained below. However, in the universe containing `Set`
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
  which contains them both due to cumulativity.
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
*)

Fail Check idSet (forall t : Set, t -> t) idSet.

(*
  ```
  The command has indeed failed with message:
  The term "forall t : Set, t -> t" has type "Type"
  while it is expected to have type "Set"
  (universe inconsistency: Cannot enforce Set+1 <= Set).
  ```

  When we write `Type`, Coq automatically figures out which level `i` should be
  used. In fact, there is no way to explicitly specify it.

  Let's fix some particular universe and let Coq choose some level `i` for it.
*)

Definition universe := Type.

(* Here's an identity function for that universe: *)

Definition idUniverse (t : universe) (x : t) := x.

(* Like with `idSet`, predicativity forbids the following: *)

Fail Check idUniverse (forall t : universe, t -> t) idUniverse.

(*
  ```
  The command has indeed failed with message:
  The term "forall t : universe, t -> t" has type "Type"
  while it is expected to have type "universe"
  (universe inconsistency: Cannot enforce universe.u0 < universe.u0 because
  universe.u0 = universe.u0).
  ```
*)

(*********************************)
(* Universes and inductive types *)
(*********************************)

(* Let's define a universe larger than `Set`. *)

Definition large := Type.

Definition constraint : large := Set.

(*
  If an inductive type in `Type_i` has a constructor which takes an argument of
  type `T` in universe `Type_j`, `i` must be at least as large as `j`.
  Parameter arguments are not considered.
*)

Inductive foo1 : Set :=
| makeFoo1 : nat -> foo1.

Fail Inductive foo2 : Set :=
| makeFoo2 : Set -> foo2.

(*
  ```
  The command has indeed failed with message:
  Large non-propositional inductive types must be in Type.
  ```
*)

Inductive foo3 : large :=
| makeFoo3 : Set -> foo3.

(* This restriction doesn't apply to inductive types in `Prop`. *)

Inductive foo4 : Prop :=
| makeFoo4 : Set -> foo4.

(*
  There are no constraints between the universe of an inductive type and the
  universes of its indices.
*)

Inductive foo5 : large -> Set :=
| makeFoo5 : foo5 Set.

Inductive foo6 : large -> Prop :=
| makeFoo6 : foo6 Set.

(*
  There are no constraints between the universe of an inductive type and the
  universes of its parameters.
*)

Inductive foo7 (x : large) : Set :=
| makeFoo7 : foo7 x.

Inductive foo8 (x : large) : Prop :=
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

(* However, the following is not allowed: *)

Fail Inductive bad :=
| makeBad : (bad -> nat) -> bad.

(*
  ```
  The command has indeed failed with message:
  Non strictly positive occurrence of "bad" in "(bad -> nat) -> bad".
  ```

  Why does coq reject `bad`? Suppose it were allowed. Consider the following
  function:

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
*)

Fail Inductive alsoBad :=
| makeAlsoBad : ((alsoBad -> nat) -> nat) -> alsoBad.

(*
  `alsoBad` could be used to construct a diverging function in an impredicative
  universe, as demonstrated in this paper:

    Coquand, T., Paulin, C. (1990). Inductively defined types. In: Martin-Löf,
    P., Mints, G. (eds) COLOG-88. COLOG 1988. Lecture Notes in Computer
    Science, vol 417. Springer, Berlin, Heidelberg.
    https://doi.org/10.1007/3-540-52335-9_47

  `alsoBad` is not known to cause any theoretical issues in predicative
  universes, but Coq still rejects it regardless of the universe in which it's
  defined.
*)

(*************)
(* Exercises *)
(*************)

(*
  1. Explain why Coq requires that all functions terminate on all inputs. How
     does Coq enforce this?
  2. No type can be its own type, yet `Check Type` reports `Type : Type`.
     What's really going on here?
  3. Describe cumulativity. Can you think of an example in which it's useful?
  4. Describe impredicativity. Does `Set` have it? Does `Prop` have it? Do the
     `Type` universes have it?
  5. Describe the restrictions Coq imposes on inductive data types.
*)

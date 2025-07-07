(*****************************************************************************)
(*****************************************************************************)
(****                                                                     ****)
(****   Restrictions imposed by Rocq to ensure consistency of the logic   ****)
(****                                                                     ****)
(*****************************************************************************)
(*****************************************************************************)

(********************************************************)
(* All functions must be statically known to terminate. *)
(********************************************************)

(* Rocq rejects all nonterminating functions, such as: *)

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

  To prevent this, Rocq requires that recursive functions have some argument
  which is structurally "decreasing" at every recursive call. Rocq can
  automatically figure out which argument that is.
*)

(****************************************************)
(* A brief summary of the universe behavior in Rocq *)
(****************************************************)

(*
  Consider a type, such as `nat`. What is its type? Suppose we call it `Type`,
  so `nat : Type`. Then what is the type of `Type`?

  One might guess that `Type` is its own type, i.e., `Type : Type`. However, in
  a rather convoluted way, this would allow one to define a nonterminating
  function and prove `False`. This is called Girard's paradox, and you can find
  it in this repo at [file:proofs/type_theory/girard.v].

  So, instead of having `Type : Type`, we have an infinite hierarchy of
  universes `Type_i` for all `i` >= 0. For convenience, universes are
  cumulative, so `T : Type_i` implies `T : Type_{i+1}`. `Type_0` is called
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

Definition IdProp (T : Prop) (x : T) := x.
Definition IdSet  (T : Set) (x : T) := x.

(* Because `Prop` is impredicative, we can apply `IdProp` to itself. *)

Check IdProp (forall T : Prop, T -> T) IdProp. (* `forall t : Prop, t -> t` *)

(*
  But `Set` (a.k.a. `Type_0`) is predicative, so we can't apply `IdSet` to
  itself:
*)

Fail Check IdSet (forall T : Set, T -> T) IdSet.

(*
  ```
  The command has indeed failed with message:
  The term "forall T : Set, T -> T" has type "Type"
  while it is expected to have type "Set"
  (universe inconsistency: Cannot enforce Set+1 <= Set).
  ```

  When we write `Type`, Rocq automatically figures out which level `i` should
  be used. In fact, there is no way to explicitly specify it.

  Let's fix some particular universe and let Rocq choose some level `i` for it.
*)

Definition U := Type.

(* Here's an identity function for that universe: *)

Definition IdU (T : U) (x : T) := x.

(* Like with `IdSet`, predicativity forbids the following: *)

Fail Check IdU (forall T : U, T -> T) IdU.

(*
  ```
  The command has indeed failed with message:
  The term "forall T : U, T -> T" has type
  "Type" while it is expected to have type
  "U" (universe inconsistency: Cannot enforce
  U.u0 < U.u0 because U.u0 = U.u0).
  ```
*)

(*********************************)
(* Universes and inductive types *)
(*********************************)

(* Let's define a universe larger than `Set`. *)

Definition Large := Type.

Definition Constraint : Large := Set.

(*
  If an inductive type in `Type_i` has a constructor which takes an argument of
  type `T` in universe `Type_j`, `i` must be at least as large as `j`.
  Parameter arguments are not considered.
*)

Inductive Foo1 : Set :=
| make_foo1 : nat -> Foo1.

Fail Inductive Foo2 : Set :=
| make_foo2 : Set -> Foo2.

(*
  ```
  The command has indeed failed with message:
  Large non-propositional inductive types must be in Type.
  ```
*)

Inductive Foo3 : Large :=
| make_foo3 : Set -> Foo3.

(* This restriction doesn't apply to inductive types in `Prop`. *)

Inductive Foo4 : Prop :=
| make_foo4 : Set -> Foo4.

(*
  There are no constraints between the universe of an inductive type and the
  universes of its parameters.
*)

Inductive Foo5 (T : Large) : Set :=
| make_foo5 : Foo5 T.

Inductive Foo6 (T : Large) : Prop :=
| make_foo6 : Foo6 T.

(*
  There are no constraints between the universe of an inductive type and the
  universes of its indices.
*)

Inductive Foo7 : Large -> Set :=
| make_foo7 : Foo7 Set.

Inductive Foo8 : Large -> Prop :=
| make_foo8 : Foo8 Set.

(***********************************************************)
(* Inductive types have a "strict positivity requirement". *)
(***********************************************************)

(* The following type is allowed, even though it has no inhabitants. *)

Inductive Weird :=
| make_weird : Weird -> Weird.

Goal Weird -> False.
  intro.
  induction H.
  auto.
Qed.

(* This "reflexive" type is also allowed: *)

Inductive Weirder :=
| make_weirder : (nat -> Weirder) -> Weirder.

Goal Weirder -> False.
  intro.
  induction H.
  apply H.
  exact 0.
Qed.

(* However, the following is not allowed: *)

Fail Inductive Bad :=
| make_bad : (Bad -> nat) -> Bad.

(*
  ```
  The command has indeed failed with message:
  Non strictly positive occurrence of "Bad" in "(Bad -> nat) -> Bad".
  ```

  Why does Rocq reject `Bad`? Suppose it were allowed. Consider the following
  function:

  ```
  Definition evil (x : Bad) : nat :=
    match x with
    | make_bad f => f x
    end.
  ```

  We could use `evil` to construct the following diverging term:

  ```
  Definition catastrophe : nat := evil (make_bad evil).
  ```

  This is also rejected:
*)

Fail Inductive AlsoBad :=
| make_also_bad : ((AlsoBad -> nat) -> nat) -> AlsoBad.

(*
  `AlsoBad` could be used to construct a diverging function in an impredicative
  universe, as demonstrated in this paper:

    Coquand, T., Paulin, C. (1990). Inductively defined types. In: Martin-
    Löf, P., Mints, G. (eds) COLOG-88. COLOG 1988. Lecture Notes in Computer
    Science, vol 417. Springer, Berlin, Heidelberg.
    https://doi.org/10.1007/3-540-52335-9_47

  `AlsoBad` is not known to cause any theoretical issues in predicative
  universes, but Rocq still rejects it regardless of the universe in which it's
  defined.
*)

(*************)
(* Exercises *)
(*************)

(*
  1. Explain why Rocq requires that all functions terminate on all inputs. How
     does Rocq enforce this?
  2. No type can be its own type, yet `Check Type` reports `Type : Type`.
     What's really going on here?
  3. Describe cumulativity. Can you think of an example in which it's useful?
  4. Describe impredicativity. Does `Set` have it? Does `Prop` have it? Do the
     `Type` universes have it?
  5. Describe the restrictions Rocq imposes on inductive data types.
*)

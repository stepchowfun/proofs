(**********************************************)
(**********************************************)
(****                                      ****)
(****   Programming with dependent types   ****)
(****                                      ****)
(**********************************************)
(**********************************************)

(*
  For variety, some the examples in this lesson will use strings. The `string`
  type is defined in the `Coq.Strings.String` module from the standard library.
  Loading a compiled module is called "requiring" it. Once required, we can
  optionally "import" its contents into the current scope. The following
  command does both.
*)

Require Import Coq.Strings.String.

(*
  The Coq parser knows how to parse string literals, but it doesn't
  automatically know how to represent them. The next line tells Coq to
  represent them with the `string` type we just imported.
*)

Local Open Scope string_scope.

(* Here's a string: *)

Check "Hello, World!".

(*****************)
(* Type families *)
(*****************)

(*
  In Lesson 1, we saw that functions can take types as arguments. Functions can
  return types as well. Functions that return types are called *type families*.
*)

Definition boolToSet x :=
  match x with
  | true => nat
  | false => string
  end.

Check boolToSet. (* `bool -> Set` *)

Compute boolToSet true.

Compute boolToSet false.

(*
  Coq considers types *definitionally equal* if they compute to syntactically
  identical types. This notion of equality between types is the one used for
  type checking. For example, we can now give the value `42` two syntactically
  different types which are nevertheless definitionally equal:
*)

Definition age1 : nat := 42.

Definition age2 : boolToSet true := 42.

(*
  Using `boolToSet`, we can construct a function for which the return type
  depends on the argument. Note the use of the `return` keyword to specify how
  the type of the `match` expression depends on the value being matched on. In
  general, such an annotation is needed when the branches of a pattern match
  don't all have the same type.
*)

Definition weird x :=
  match x return boolToSet x with
  | true => 42
  | false => "hello"
  end.

Check weird. (* `forall x : bool, boolToSet x` *)

Compute weird true. (* `42` *)

Compute weird false. (* `"hello"` *)

(**************************************************)
(* Parameters and indices of inductive data types *)
(**************************************************)

(*
  We saw in Lesson 1 that inductive data types can have type *parameters*.
  However, parameters don't need to be types. In the following contrived
  example, the parameter is a `nat`:
*)

Inductive parameterized (x : nat) :=
| parameterizedFoo : parameterized x
| parameterizedBar : parameterized x.

Check parameterized. (* `nat -> Set` *)

(* Each constructor automatically takes the parameters as extra arguments. *)

Check parameterizedFoo. (* `forall x : nat, parameterized x` *)

Check parameterizedBar. (* `forall x : nat, parameterized x` *)

(* When pattern matching, parameters are ignored. *)

Definition parameterizedToBool n (c : parameterized n) :=
  match c with
  | parameterizedFoo _ => true
  | parameterizedBar _ => false
  end.

Check parameterizedToBool. (* `forall n : nat, parameterized n -> bool` *)

(*
  Instead of defining the type with a parameter, we could have instead defined
  it with an *index*. Unlike with parameters, indices are not automatically
  added as an extra argument to each constructor. It's up to us to add such
  arguments to each constructor.
*)

Inductive indexed : nat -> Set :=
| indexedFoo : forall x, indexed x
| indexedBar : forall x, indexed x.

Check indexed. (* `nat -> Set` *)

(*
  With indexed inductive data types, the types of the constructors are exactly
  as we specified in the definition.
*)

Check indexedFoo. (* `forall x : nat, indexed x` *)

Check indexedBar. (* `forall x : nat, indexed x` *)

(*
  So far, it seems like indices are just a more verbose form of parameters.
  However, they unlock a new power: the ability for each constructor to specify
  particular values for the indices.
*)

Inductive contrived : nat -> Set :=
| contrivedFoo : contrived 42
| contrivedBar : contrived 43.

Check contrived. (* `nat -> Set` *)

Check contrivedFoo. (* `indexed 42` *)

Check contrivedBar. (* `indexed 43` *)

Definition contrivedToBool n (c : contrived n) :=
  match c with
  | contrivedFoo => true
  | contrivedBar => false
  end.

Check contrivedToBool. (* `forall n : nat, contrived n -> bool` *)

(*
  The terminology is somewhat confusing. `parameterized` is called a *family of
  inductive types*. `indexed` and `contrived` are called *inductively defined
  families*, or *inductive families* for short. Families of inductive types,
  inductive families, and functions which return types are all called *type
  families*.
*)

(************************************)
(* Case study: length-indexed lists *)
(************************************)

(*
  Putting all this together, we're going to define a type which features both
  a parameter and an index. This type represents lists. The parameter indicates
  the type of the elements. The index indicates the length of the list.
*)

Inductive vector (T : Set) : nat -> Type :=
| empty : vector T O
| nonempty : forall n, T -> vector T n -> vector T (S n).

(*
  Make the `T` and `n` arguments implicit in `nonempty`, since they can be
  determined automatically from the tail.
*)

Arguments nonempty {_} {_} _ _.

(* Let's construct some `vector`s. *)

Check empty bool. (* `vector bool 0` *)
Check nonempty true (empty bool). (* `vector bool 1` *)
Check nonempty false (nonempty true (empty bool)). (* `vector bool 2` *)

(* Here's a function which produces a `vector` of zeros of a given length. *)

Fixpoint zeroes n1 :=
  match n1 with
  | O => empty nat
  | S n2 => nonempty 0 (zeroes n2)
  end.

Check zeroes. (* `forall n1 : nat, vector nat n1` *)

Compute zeroes 3. (* `nonempty 0 (nonempty 0 (nonempty 0 (empty nat)))` *)

(*
  Here's a function which concatenates two `vector`s. This demonstrates how to
  do dependent pattern matching.
*)

Fixpoint concatenate
           {T n1 n2}
           (v1 : vector T n1)
           (v2 : vector T n2) :
           vector T (n1 + n2) :=
  match v1
  in vector _ n3 (* Bind the length of the `vector` to `n3`. *)
  return vector T (n3 + n2) (* `n3` = `n1` *)
  with
  | empty _ => v2 (* `n3` = `0` *)
  | nonempty x v3 => nonempty x (concatenate v3 v2) (* `n3` = `S (len v3)` *)
  end.

(*
  Here's a function which returns the first element of a `vector`. It's a type
  error to call this function on an empty `vector`.
*)

Definition head {T n} (v : vector T (S n)) : T :=
  match v with
  | nonempty x _ => x
  end.

(*
  You might have noticed we didn't handle the `empty` case! What's going on
  here?
*)

Print head.

(*
  ```
  fun (T : Set) (n : nat) (v : vector T (S n)) =>
    match v
    in (vector _ n0)
    return match n0 with
           | 0 => IDProp
           | S _ => T
           end
    with
    | empty _ => idProp
    | @nonempty _ n0 x _ => x
    end
  ```

  Coq is smart enough to know the `empty` case is impossible, so it handles it
  automatically with a dummy value (`idProp`). The dummy value doesn't have the
  same type as the `nonempty` case, so this is a dependent pattern match.

  Let's try it out on a simple example.
*)

Compute head (nonempty true (empty bool)). (* `true` *)

(*
  The following doesn't type check:

  ```
  Compute head (empty bool).
  ```
*)

(*************)
(* Exercises *)
(*************)

(*
  1. Explain the differences between parameters and indices. When should you
     use one over the other?
  2. Define a `tail` function which takes a `vector` and returns a new `vector`
     with the contents of the original `vector` but without the head. It should
     work with any vector as its input, including the empty vector.
*)

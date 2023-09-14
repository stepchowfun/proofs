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
  optionally "import" its contents into the current scope so we don't have to
  use fully qualified names. The following command does both.
*)

Require Import Coq.Strings.String.

(*
  The Coq parser knows how to parse string literals, but it doesn't
  automatically know how to represent them. The next line tells Coq to
  represent them with the `string` type we just imported.
*)

#[local] Open Scope string_scope.

(* Here's a string: *)

Check "Hello, World!". (* `string` *)

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

Compute boolToSet true. (* `nat` *)

Compute boolToSet false. (* `string` *)

(*
  Coq considers types *definitionally equal* if they compute to syntactically
  identical types. This notion of equality between types is the one used for
  type checking. For example, we can give the value `42` the following two
  types which are definitionally equal:
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

(*
  If the expression being matched on is not a variable and we want to use it in
  the `return` clause, we must bind a variable to it using an `as` clause.
*)

Definition weirder x :=
  match negb x as y return boolToSet y with
  | true => 42
  | false => "hello"
  end.

Check weirder. (* `forall x : bool, boolToSet (negb x)` *)

Compute weirder true. (* `"hello"` *)

Compute weirder false. (* `42` *)

(**************************************************)
(* Parameters and indices of inductive data types *)
(**************************************************)

(*
  We saw in Lesson 1 that inductive data types can have *parameters*.
  Parameters give us another way to define type families.
*)

Inductive option (T : Set) :=
| none : option T
| some : T -> option T.

Check option. (* `Set -> Set` *)

(* Each constructor automatically takes the parameters as extra arguments. *)

Check none. (* `forall T : Set, option T` *)

Check some. (* `forall T : Set, T -> option T` *)

(* When pattern matching, ignore parameter arguments with `_`. *)

Definition unwrap (o : option nat) :=
  match o with
  | none _ => 0
  | some _ x => x
  end.

Check unwrap. (* `option nat -> nat` *)

(*
  A third way to define type families is to use *indices*. Indices are like
  parameters, but they unlock a new power: each constructor specifies a value
  for the index. Consider the following example:
*)

Inductive boolOrNat : Set -> Set :=
| someBool : bool -> boolOrNat bool
| someNat : nat -> boolOrNat nat.

Check boolOrNat. (* `Set -> Set` *)

Check someBool. (* `bool -> boolOrNat bool` *)

Check someNat. (* `nat -> boolOrNat nat` *)

(*
  When pattern matching, we can use an `in` clause to bind variables to the
  indices so they can be used in the `return` clause. In the following example,
  we bind the variable `U` to the index and use that as the return type. This
  may seem silly since the index is already a variable (`T`), but in general it
  could be an arbitrary expression.
*)

Definition pluck {T : Set} (x : boolOrNat T) :=
  match x in boolOrNat U return U with
  | someBool b => b
  | someNat n => n
  end.

Check pluck. (* `boolOrNat ?T -> ?T` *)

Compute pluck (someNat 42). (* `42` *)

(*
  The terminology is somewhat confusing. `option` is called a *family of
  inductive types*. `boolOrNat` is called an *inductively defined family*, or
  *inductive family* for short. Families of inductive types, inductive
  families, and functions which return types are all called *type families*.
*)

(************************************)
(* Case study: length-indexed lists *)
(************************************)

(*
  Putting all this together, we're going to define a type which features both
  a parameter and an index. This type represents lists. The parameter indicates
  the type of the elements. The index indicates the length of the list. Lists
  which feature their length in their type are called *vectors*:
*)

Inductive vector (T : Set) : nat -> Set :=
| empty : vector T O
| nonempty : forall n, T -> vector T n -> vector T (S n).

(*
  Make the `T` and `n` arguments implicit in `nonempty`, since they can be
  determined automatically from the tail.
*)

Arguments nonempty {_ _} _ _.

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

(* Here's a function which concatenates two `vector`s. *)

Fixpoint concatenate
           {T n1 n2}
           (v1 : vector T n1)
           (v2 : vector T n2) :
           vector T (n1 + n2) :=
  match v1 in vector _ n3 return vector T (n3 + n2) with
  | empty _ => v2
  | nonempty x v3 => nonempty x (concatenate v3 v2)
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

(* By design, we can't take the `head` of an empty vector: *)

Fail Compute head (empty bool).

(*
  ```
  The command has indeed failed with message:
  The term "empty bool" has type "vector bool 0"
  while it is expected to have type "vector bool (S ?n)".
  ```
*)

(*************)
(* Exercises *)
(*************)

(*
  1. Explain the differences between parameters and indices. When should you
     use one over the other?
  2. When pattern matching, what does `return` do? What does `as` do? What does
     `in` do?
  3. Define a `tail` function which takes a `vector` and returns a new `vector`
     with the contents of the original `vector` but without the head. It should
     work with any vector as its input, including the empty vector.
*)

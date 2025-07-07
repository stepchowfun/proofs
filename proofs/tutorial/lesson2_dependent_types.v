(**********************************************)
(**********************************************)
(****                                      ****)
(****   Programming with dependent types   ****)
(****                                      ****)
(**********************************************)
(**********************************************)

(*
  For variety, some the examples in this lesson will use strings. The `string`
  type is defined in the `Rocq.Strings.String` module from the standard
  library.  Loading a compiled module is called "requiring" it. Once required,
  we can optionally "import" its contents into the current scope so we don't
  have to use fully qualified names. The following command does both.
*)

Require Import Stdlib.Strings.String.

(*
  The Rocq parser knows how to parse string literals, but it doesn't
  automatically know how to represent them. The next line tells Rocq to
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

Definition BoolToType x :=
  match x with
  | true => nat
  | false => string
  end.

Check BoolToType. (* `bool -> Set` *)

Compute BoolToType true. (* `nat` *)

Compute BoolToType false. (* `string` *)

(*
  Rocq considers types *definitionally equal* if they compute to syntactically
  identical types. This notion of equality between types is the one used for
  type checking. For example, we can give the value `42` the following two
  types which are definitionally equal:
*)

Definition age1 : nat := 42.

Definition age2 : BoolToType true := 42.

(*
  Using `BoolToType`, we can construct a function for which the return type
  depends on the argument. Note the use of the `return` keyword to specify how
  the type of the `match` expression depends on the value being matched on. In
  general, such an annotation is needed when the branches of a pattern match
  don't all have the same type.
*)

Definition weird x :=
  match x return BoolToType x with
  | true => 42
  | false => "hello"
  end.

Check weird. (* `forall x : bool, BoolToType x` *)

Compute weird true. (* `42` *)

Compute weird false. (* `"hello"` *)

(*
  If the expression being matched on is not a variable and we want to use it in
  the `return` clause, we must bind a variable to it using an `as` clause.
*)

Definition weirder x :=
  match negb x as y return BoolToType y with
  | true => 42
  | false => "hello"
  end.

Check weirder. (* `forall x : bool, BoolToType (negb x)` *)

Compute weirder true. (* `"hello"` *)

Compute weirder false. (* `42` *)

(**************************************************)
(* Parameters and indices of inductive data types *)
(**************************************************)

(*
  We saw in Lesson 1 that inductive data types can have *parameters*.
  Parameters give us another way to define type families.
*)

Inductive Option (T : Set) :=
| none : Option T
| some : T -> Option T.

Check Option. (* `Set -> Set` *)

(* Each constructor automatically takes the parameters as extra arguments. *)

Check none. (* `forall T : Set, Option T` *)

Check some. (* `forall T : Set, T -> Option T` *)

(* When pattern matching, ignore parameter arguments with `_`. *)

Definition unwrap (o : Option nat) :=
  match o with
  | none _ => 0
  | some _ x => x
  end.

Check unwrap. (* `Option nat -> nat` *)

(*
  A third way to define type families is to use *indices*. Indices are like
  parameters, but they unlock a new power: each constructor specifies a value
  for the index. Consider the following example:
*)

Inductive BoolOrNat : Set -> Set :=
| some_bool : bool -> BoolOrNat bool
| some_nat : nat -> BoolOrNat nat.

Check BoolOrNat. (* `Set -> Set` *)

Check some_bool. (* `bool -> BoolOrNat bool` *)

Check some_nat. (* `nat -> BoolOrNat nat` *)

(*
  When pattern matching, we can use an `in` clause to bind variables to the
  indices so they can be used in the `return` clause. In the following example,
  we bind the variable `U` to the index and use that as the return type. This
  may seem silly since the index is already a variable (`T`), but in general it
  could be an arbitrary expression.
*)

Definition pluck [T : Set] (x : BoolOrNat T) :=
  match x in BoolOrNat U return U with
  | some_bool b => b
  | some_nat n => n
  end.

Check pluck. (* `forall T : Set, BoolOrNat T -> T` *)

Compute pluck (some_nat 42). (* `42` *)

(*
  The terminology is somewhat confusing. `Option` is called a *family of
  inductive types*. `BoolOrNat` is called an *inductively defined family*, or
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

Inductive Vector (T : Set) : nat -> Set :=
| empty : Vector T O
| nonempty : forall n, T -> Vector T n -> Vector T (S n).

(*
  Make the `T` and `n` arguments implicit in `nonempty`, since they can be
  determined automatically from the tail.
*)

Arguments nonempty [_ _] _ _.

(* Let's construct some `Vector`s. *)

Check empty bool. (* `Vector bool 0` *)
Check nonempty true (empty bool). (* `Vector bool 1` *)
Check nonempty false (nonempty true (empty bool)). (* `Vector bool 2` *)

(* Here's a function which produces a `Vector` of zeros of a given length. *)

Fixpoint zeroes n1 :=
  match n1 with
  | O => empty nat
  | S n2 => nonempty 0 (zeroes n2)
  end.

Check zeroes. (* `forall n1 : nat, Vector nat n1` *)

Compute zeroes 3. (* `nonempty 0 (nonempty 0 (nonempty 0 (empty nat)))` *)

(* Here's a function which concatenates two `Vector`s. *)

Fixpoint concatenate
           [T n1 n2]
           (v1 : Vector T n1)
           (v2 : Vector T n2) :
           Vector T (n1 + n2) :=
  match v1 in Vector _ n3 return Vector T (n3 + n2) with
  | empty _ => v2
  | nonempty x v3 => nonempty x (concatenate v3 v2)
  end.

(*
  Here's a function which returns the first element of a `Vector`. It's a type
  error to call this function on an empty `Vector`.
*)

Definition head [T n] (v : Vector T (S n)) : T :=
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
  fun (T : Set) (n : nat) (v : Vector T (S n)) =>
    match v
    in (Vector _ n0)
    return match n0 with
           | 0 => IDProp
           | S _ => T
           end
    with
    | empty _ => idProp
    | @nonempty _ n0 x _ => x
    end
  ```

  Rocq is smart enough to know the `empty` case is impossible, so it handles it
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
  The term "empty bool" has type "Vector bool 0"
  while it is expected to have type "Vector bool (S ?n)".
  ```
*)

(**********************)
(* The convoy pattern *)
(**********************)

(* Suppose we have a number `n`. *)

Parameter n : nat.

(*
  The following variable `x` has an interesting type. When `n` is even, `x` is
  a `nat`. Conversely, when `n` is odd, `x` is a `string`. However, the parity
  of `n` is unknown here, so `x` seems to have some kind of superposition of
  types.
*)

Parameter x : BoolToType (Nat.even n).

(*
  Suppose we want to do something with `x`. Since the type of `x` depends on
  whether `n` is even or odd, we should expect to handle those two cases
  separately. For example, if `n` is even, we might want to do some arithmetic
  with `x`, since it's a `nat` in that case. Otherwise, `x` is a string, and
  perhaps we wish to compute its length. Unfortunately, we can't do that by
  naively pattern matching on the parity of `n`:
*)

Fail Check
  match Nat.even n with
  | true => x + 1
  | false => length x
  end.

(*
  ```
  The command has indeed failed with message:
  The term "x" has type "BoolToType (Nat.even n)"
  while it is expected to have type "nat".
  ```

  The issue is that Rocq doesn't refine the type of `x` based on the knowledge
  gained about the parity of `n` in each case. To make the example work, we can
  use the *convoy pattern*. First, we use dependent pattern matching to
  construct a function which accepts an arbitrary `BoolToType (Nat.even n)`,
  then we immediately call that function on `x`. Dependent pattern matching
  specializes the type of the result on each case, so each branch only needs to
  consider the specific value of `Nat.even n` (`true` or `false`) corresponding
  to that case.
*)

Check
  match Nat.even n as b return BoolToType b -> _ with
  | true => fun y => y + 1
  | false => fun y => length y
  end x.

(*************)
(* Exercises *)
(*************)

(*
  1. Explain the differences between parameters and indices. When should you
     use one over the other?
  2. When pattern matching, what does `return` do? What does `as` do? What does
     `in` do?
  3. Define a `tail` function which takes a `Vector` and returns a new `Vector`
     with the contents of the original `Vector` but without the head. It should
     work with any `Vector` as its input, including the empty `Vector`.
*)

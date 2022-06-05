(****************************************************)
(****************************************************)
(****                                            ****)
(****   Ordinary functional programming in Coq   ****)
(****                                            ****)
(****************************************************)
(****************************************************)

(***************************)
(* Variables and functions *)
(***************************)

(*
  Sometimes it's useful to ask Coq for the type of an expression. We can use
  the `Check` command for that. In this case, the type is `nat`, which stands
  for "natural number". Natural numbers are non-negative integers, and they're
  the most common type of number in Coq.
*)

Check 3 + 4. (* `nat` *)

(* If we want Coq to actually evaluate an expression, we can use `Compute`. *)

Compute 3 + 4. (* `7` *)

(*
  We can define variables with the `Definition` keyword. Note that Coq is able
  to infer the type of this variable automatically.
*)

Definition myVariable := 42.

(*
  Functions are data too, so we can also use `Definition` to introduce
  functions. Note that Coq is able to infer that the type of the function is
  `nat -> nat` based on how `+` is used in the body.
*)

Definition double := fun x => x + x.

Check double. (* `nat -> nat` *)

(* Here's a more convenient syntax that does the same thing. *)

Definition betterDouble x := x + x.

Check betterDouble. (* `nat -> nat` *)

(*
  To call a function `f` on some input `x`, we simply write `f x`. Note that
  we don't need parentheses, unlike in other languages.
*)

Compute double myVariable. (* `84` *)

(*
  In Coq, every function takes exactly one argument. However, we can use
  "currying" to represent functions of multiple arguments as nested functions.
  Suppose we want to define a function of two arguments. We can write it as a
  function which takes only the first argument and returns another function
  which takes the second argument to the final result.
*)

Definition multiply := fun x => fun y => x * y.

Check multiply. (* `nat -> nat -> nat` *)

(*
  Note that `nat -> nat -> nat` should be understood as `nat -> (nat -> nat)`,
  not `(nat -> nat) -> nat`.

  Coq has a more convenient syntax for defining curried functions like this:
*)

Definition betterMultiply x y := x * y.

Check betterMultiply. (* `nat -> nat -> nat` *)

(*
  To call a curried function `f` with two arguments `x` and `y`, write `f x y`.
  This should be understood as `(f x) y`, not `f (x y)`.
*)

Compute multiply 3 4. (* `12` *)

(* Currying works with any positive integer number of arguments. *)

Definition addAndMultiply x y z := x + y * z.

Check addAndMultiply. (* `nat -> nat -> nat -> nat` *)

Compute addAndMultiply 3 4 5. (* `23` *)

(*
  Sometimes, the type of a function's argument is ambiguous.

  ```
  Definition id x := x.
  ```

  To resolve this ambiguity, we need to provide a type annotation.
*)

Definition idNat (x : nat) := x.

Check idNat. (* `nat -> nat` *)

Definition idBool (x : bool) := x.

Check idBool. (* `nat -> nat` *)

(*
  Those identity functions are almost exactly the same, except they're defined
  on different types. Wouldn't it be nice to define a universal identity
  function that works on all types? It turns out that types are data, just like
  numbers and functions. So all we need to do is take the type as an extra
  argument. This idea is called "generics" or "templates" in some other
  languages.
*)

Definition id (T : Set) (x : T) := x.

Compute id nat (3 + 4). (* `7`*)

(*
  What's the type of `id`? `id` is a curried function of two arguments, but the
  type of the second argument isn't fixed; it *depends* on the first argument,
  which isn't known here since it's provided by the caller. Thus, in the type
  of `id`, we need to give a name to the first argument so we can refer to it
  in the type of the second argument. The `forall` keyword does exactly that.
*)

Check id. (* `forall T : Set, T -> T` *)

(*
  `A -> B` is actually just shorthand for `forall x : A, B`, as long as `B`
  doesn't refer to `x`. We can write the type of `id` in any of the following
  equivalent ways:

  - `forall T : Set, T -> T`
  - `forall T : Set, forall x : T, T`
  - `forall (T : Set) (x : T), T`

  The first way is generally best.

  It's awkward to have to explicitly provide the type argument whenever we call
  the `id` function. We can declare the argument *implicit* by using curly
  braces instead of parentheses. Then Coq will try to figure it out
  automatically whenever we use the function.
*)

Definition betterId {T : Set} (x : T) := x.

Check betterId. (* `?T -> ?T where ?T : [ |- Set]` *)

Compute betterId (3 + 4). (* `7` *)

(*******************************)
(* Simple inductive data types *)
(*******************************)

(*
  An *inductive data type* is defined by cases, called *constructors*. For
  example, we can define a type called `bool` with two constructors: `true` and
  `false`. The standard library already defines this type, but we'll redefine
  it here to demonstrate how inductive data types work.
*)

Inductive bool :=
| true
| false.

Check true. (* `bool` *)

Check false. (* `bool` *)

Check bool. (* `Set` *)

(*
  To use a `bool`, we can do case analysis on it. This is called *pattern
  matching*. For example, we can use pattern matching to define a function
  which inverts a `bool`.
*)

Definition flip b :=
  match b with
  | true => false
  | false => true
  end.

Compute flip true. (* `false` *)

Compute flip false. (* `true` *)

(*
  For inductive data types with exactly two constructors (like `bool`), we can
  use `if`/`then`/`else`. Note that we had to add a type annotation to the
  argument `b`, since `if`/`then`/`else` works on other types too.
*)

Definition betterFlip (b : bool) := if b then false else true.

(*
  Each case of an inductive data type may store some data. In order to use that
  feature, we can provide a type annotation each constructor describing what
  data that constructor accepts. For example, we can define a type which *may*
  hold a `nat` as follows:
*)

Inductive optionNat :=
| NoneNat : optionNat
| SomeNat : nat -> optionNat.

Check NoneNat. (* optionNat *)

Check SomeNat. (* nat -> optionNat *)

Check SomeNat 3. (* optionNat *)

Check optionNat. (* `Set` *)

(*
  When pattern matching on an `optionNat`, we get access to the `nat` in the
  `Some` case. Here is a function which will transform the `nat`, if it exists,
  by a user-provided function.
*)

Definition mapOptionNat f o :=
  match o with
  | NoneNat => NoneNat
  | SomeNat n => SomeNat (f n)
  end.

Check mapOptionNat. (* `(nat -> nat) -> optionNat -> optionNat` *)

Compute mapOptionNat double (SomeNat 3). (* `SomeNat 6` *)

Compute mapOptionNat double NoneNat. (* `NoneNat` *)

(*
  `optionNat` only works with `nat`s. We can add a type parameter to make it
  work for any type.
*)

Inductive option (T : Set) :=
| None : option T
| Some : T -> option T.

Check None. (* `forall T : Set, option T` *)

Check Some. (* `forall T : Set, T -> option T` *)

Check option. (* `Set -> Set` *)

Definition mapOption {T} f (o : option T) :=
  match o with
  | None _ => None T
  | Some _ x => Some T (f x)
  end.

Check mapOption. (* `(?T -> ?T) -> option ?T -> option ?T` *)

Compute mapOption (fun n => n + 1) (None nat). (* `None nat` *)

Compute mapOption (fun n => n + 1) (Some nat 3). (* `Some nat 4` *)

Compute mapOption flip (Some bool false). (* `Some bool true` *)

(*
  The type argument for `Some` can be deduced automatically from the payload,
  so we can make it implicit as follows.
*)

Arguments Some {_} _.

Check Some. (* `?T -> option ?T where ?T : [ |- Set]` *)

Compute mapOption (fun n => n + 1) (Some 3). (* `Some 4` *)

Compute mapOption flip (Some false). (* `Some true` *)

(*
  Inductive types can be recursive. For example, below is how natural numbers
  are defined in the standard library. Note that the name of the first
  constructor is the letter "O", which was chosen due to its resemblance to the
  numeral "0".
*)

Inductive nat :=
| O : nat (* Zero *)
| S : nat -> nat. (* Successor of another `nat` *)

Check nat. (* `Set` *)
Check O. (* `nat` *)
Check S. (* `nat -> nat` *)
Check S O. (* `nat` *)
Check S (S O). (* `nat` *)
Check S (S (S O)). (* `nat` *)

(*
  Conveniently, the Coq parser allows us to write numeric literals instead of
  `S (S (S (...)))`. Numbers written this way use the `nat` type from the
  standard library, rather than the one we defined above.
*)

Check 0. (* `Datatypes.nat` *)
Check 1. (* `Datatypes.nat` *)
Check 2. (* `Datatypes.nat` *)

(*
  Addition can be defined recursively. Note that recursive definitions use the
  `Fixpoint` keyword instead of `Definition`.
*)

Fixpoint add n m :=
  match n with
  | O => m
  | S p => S (add p m)
  end.

(* Let's compute 1 + 1. *)

Compute add (S O) (S O). (* `S (S O)` *)

(* If we use `nat`s from the standard library, we get nice numeric literals. *)

Compute 1 + 1. (* `2` *)
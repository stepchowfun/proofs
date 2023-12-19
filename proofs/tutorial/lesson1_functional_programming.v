(*********************************************)
(*********************************************)
(****                                     ****)
(****   Ordinary functional programming   ****)
(****                                     ****)
(*********************************************)
(*********************************************)

(***************************)
(* Variables and functions *)
(***************************)

(*
  Sometimes it's useful to ask Coq for the type of an expression. We can use
  the `Check` command for that. For example, the type of the expression below
  is `nat`, which stands for "natural number". Natural numbers are unsigned
  integers, and they're the most common type of number in Coq.

  To use these commands interactively, be sure you're using an IDE that
  supports Coq, such as CoqIDE or Visual Studio Code with the VsCoq plugin.
*)

Check 3 + 4. (* `nat` *)

(* If we want Coq to actually evaluate an expression, we can use `Compute`. *)

Compute 3 + 4. (* `7` *)

(*
  We can define variables with the `Definition` keyword. Coq is able to infer
  that the type of this variable is `nat`.
*)

Definition my_variable := 42.

Check my_variable. (* `nat` *)

(*
  Functions are data too, so we can also use `Definition` to introduce
  functions. Coq is able to infer that the type of this function is
  `nat -> nat` based on how `+` is used in the body.
*)

Definition double := fun x => x + x.

Check double. (* `nat -> nat` *)

(* Here's a more convenient syntax that does the same thing. *)

Definition better_double x := x + x.

Check better_double. (* `nat -> nat` *)

(*
  To call a function `f` on some input `x`, we simply write `f x`. Note that
  we don't need parentheses, unlike in other languages.
*)

Compute double my_variable. (* `84` *)

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

Definition better_multiply x y := x * y.

Check better_multiply. (* `nat -> nat -> nat` *)

(*
  To call a curried function `f` with two arguments `x` and `y`, write `f x y`.
  This should be understood as `(f x) y`, not `f (x y)`.
*)

Compute multiply 3 4. (* `12` *)

(* Currying works with any positive integer number of arguments. *)

Definition add_and_multiply x y z := x + y * z.

Check add_and_multiply. (* `nat -> nat -> nat -> nat` *)

Compute add_and_multiply 3 4 5. (* `23` *)

(*
  Sometimes, the type of a function's argument can't be inferred automatically.
  For example, the following ambiguous definition is rejected:
*)

Fail Definition id x := x.

(*
  ```
  The command has indeed failed with message:
  The following term contains unresolved implicit arguments:
    (fun x : ?T => x)
  More precisely:
  - ?T: Cannot infer the type of x.
  ```

  To resolve this ambiguity, we need to provide a type annotation for `x`:
*)

Definition id_nat (x : nat) := x.

Check id_nat. (* `nat -> nat` *)

Definition id_bool (x : bool) := x.

Check id_bool. (* `bool -> bool` *)

(*
  Those identity functions are almost exactly the same, except they're defined
  on different types. Wouldn't it be nice to define a universal identity
  function that works on all types? It turns out that types are data, just like
  numbers and functions. So all we need to do is take the type as an extra
  argument. The type of that argument will be `Set`, which is the type of types
  like `nat`, `bool`, `nat -> bool`, and so on. A type which has types as
  members is called a *universe*. Lesson 5 discusses universes in depth.

  The idea of parameterizing a definition by a type is known as "generics" in
  many languages, e.g., Java and Rust.
*)

Definition id (T : Set) (x : T) := x.

Compute id nat (3 + 4). (* `7` *)

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

  The first way is best, since it makes it clear that the return type doesn't
  depend on the value of the second argument.

  It's awkward to have to explicitly provide the type argument whenever we call
  the `id` function. We can declare the argument *implicit* by using curly
  braces instead of parentheses. Then Coq will try to figure it out
  automatically whenever we use the function.
*)

Definition better_id [T : Set] (x : T) := x.

Check better_id. (* `?T -> ?T where ?T : [|- Set]` *)

Compute better_id (3 + 4). (* `7` *)

(*
  If Coq is unable to infer the implicit arguments, we can pass them explicitly
  by prefixing the function with `@`.
*)

Compute @better_id nat (3 + 4). (* `7` *)

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
  matching*. For example, we can use pattern matching to define a function that
  inverts a `bool`.
*)

Definition negb b :=
  match b with
  | true => false
  | false => true
  end.

Compute negb true. (* `false` *)

Compute negb false. (* `true` *)

(*
  Each case of an inductive data type may store some data. In order to use that
  feature, we can provide a type annotation for each constructor describing
  what data that constructor accepts. For example, we can define a type such
  that its elements *might* hold a `nat` as follows:
*)

Inductive OptionNat :=
| no_nat : OptionNat
| some_nat : nat -> OptionNat.

Check no_nat. (* `OptionNat` *)

Check some_nat. (* `nat -> OptionNat` *)

Check some_nat 3. (* `OptionNat` *)

Check OptionNat. (* `Set` *)

(*
  When pattern matching on an `OptionNat`, we get access to the `nat` in the
  `some` case. Here is a function which will transform the `nat`, if it exists,
  by a user-provided function.
*)

Definition map_option_nat f o :=
  match o with
  | no_nat => no_nat
  | some_nat n => some_nat (f n)
  end.

Check map_option_nat. (* `(nat -> nat) -> OptionNat -> OptionNat` *)

Compute map_option_nat double (some_nat 3). (* `some_nat 6` *)

Compute map_option_nat double no_nat. (* `no_nat` *)

(*
  `OptionNat` only works with `nat`s. We can add a type *parameter* to make it
  work for any type. This results in a family of inductive data types, one for
  every choice of `T`. Note that each constructor returns an `option T`, rather
  than just an `option`.
*)

Inductive option (T : Set) :=
| none : option T
| some : T -> option T.

(*
  Each constructor automatically takes the parameter as an extra argument.
  Thus, if we check the type of each constructor, we find it doesn't exactly
  match the type we provided in the definition.
*)

Check none. (* `forall T : Set, option T` *)

Check none bool. (* `option bool` *)

Check some. (* `forall T : Set, T -> option T` *)

Check some bool true. (* `option bool` *)

Check option. (* `Set -> Set` *)

(*
  When pattern matching on an `option T`, add a `_` to each pattern to account
  for the parameter argument.
*)

Definition map_option [T U] f (o : option T) :=
  match o with
  | none _ => none U
  | some _ x => some U (f x)
  end.

Check map_option. (* `(?T -> ?U) -> option ?T -> option ?U` *)

Compute map_option (fun n => n + 1) (none nat). (* `none nat` *)

Compute map_option (fun n => n + 1) (some nat 3). (* `some nat 4` *)

Compute map_option negb (some bool false). (* `some bool true` *)

Compute map_option (fun n => true) (some nat 3). (* `some bool true` *)

(*
  The type argument for `some` can be deduced automatically from its other
  argument, so we can make it implicit as shown below. We couldn't do this with
  curly braces in the definition, since this type argument was automatically
  added by Coq as a consequence of it being a parameter. We could have made the
  parameter implicit, but that would have affected `none` and `option` too.
*)

Arguments some [_] _.

Check some. (* `?T -> option ?T where ?T : {|- Set]` *)

Compute map_option (fun n => n + 1) (some 3). (* `some 4` *)

Compute map_option negb (some false). (* `some true` *)

(*
  Inductive data types can be recursive. For example, below is how natural
  numbers are defined in the standard library. Note that the name of the first
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

(*
  By default, the parser is configured to parse numeric literals into natural
  numbers, but using the definition from the standard library rather than our
  identical definition above. So, when working with natural numbers from the
  standard library, we don't have to write all those `S`s. The standard library
  also defines the `+` operator as shorthand for `add`, so we can simply write:
*)

Compute 1 + 1. (* `2` *)

(*************)
(* Exercises *)
(*************)

(*
  1. Define the concept of lists as an inductive data type which is
     parameterized by the element type. Which arguments would you make
     implicit, if any?
  2. Define a function which computes the length of a list as defined in the
     previous question.
  3. Define a `map` function for lists as defined in the first question,
     analogous to the `map_option` function defined in the lesson.
  4. Define a function which compares two natural numbers for equality.
  5. Define multiplication of natural numbers.
  6. Define subtraction of natural numbers. The function should return an
     `OptionNat` (or `option nat`) to account for the fact that negative
     results can't be represented as natural numbers.
*)

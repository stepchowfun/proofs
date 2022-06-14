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

Inductive contrived (x : nat) :=
| contrivedFoo : contrived x
| contrivedBar : contrived x.

Check contrived. (* `nat -> Set` *)

Check contrivedFoo. (* `forall x : nat, contrived x` *)

Check contrivedBar. (* `forall x : nat, contrived x` *)

Definition contrivedToBool n (c : contrived n) :=
  match c with
  | contrivedFoo _ => true  (* Note the `_` for the parameter. *)
  | contrivedBar _ => false (* Note the `_` for the parameter. *)
  end.

Check contrivedToBool. (* `forall n : nat, contrived n -> bool` *)

(*
  Note that each constructor automatically takes the parameter (`x`) as an
  argument, leaving it up to the caller to decide what value it takes on. If we
  replace the parameter with an *index*, each constructor can decide what the
  value of the index should be for that particular case.
*)

Inductive alsoContrived : nat -> Set :=
| alsoContrivedFoo : alsoContrived 42
| alsoContrivedBar : alsoContrived 43.

Check alsoContrived. (* `nat -> Set` *)

Check alsoContrivedFoo. (* `alsoContrived 42` *)

Check alsoContrivedBar. (* `alsoContrived 43` *)

Definition alsoContrivedToBool n (c : alsoContrived n) :=
  match c with
  | alsoContrivedFoo => true  (* Note that there's no `_` for the index. *)
  | alsoContrivedBar => false (* Note that there's no `_` for the index. *)
  end.

Check alsoContrivedToBool. (* `forall n : nat, alsoContrived n -> bool` *)

(*
  Indices are strictly more general than parameters. For example, we can define
  the `contrived` family with an index instead of a parameter:
*)

Inductive superContrived : nat -> Set :=
| superContrivedFoo : forall x, superContrived x
| superContrivedBar : forall x, superContrived x.

Check superContrived. (* `nat -> Set` *)

Check superContrivedFoo. (* `forall x : nat, superContrived x` *)

Check superContrivedBar. (* `forall x : nat, superContrived x` *)

Definition superContrivedToBool n (c : superContrived n) :=
  match c with
  | superContrivedFoo _ => true
  | superContrivedBar _ => false
  end.

Check superContrivedToBool. (* `forall n : nat, superContrived n -> bool` *)

(*
  The terminology is somewhat confusing. `contrived`, which has a parameter, is
  called a *family of inductive types*. `alsoContrived` and `superContrived`,
  which each have an index, are called *inductively defined families*, or
  *inductive families* for short. Families of inductive types, inductive
  families, and functions which return types are all called *type families*.
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
| nil : vector T O
| cons :
    forall {n},   (* Length of the tail, implicit due to the curly braces *)
    T ->          (* Head *)
    vector T n -> (* Tail *)
    vector T (S n).

(*
  Make the `T` argument implicit in `cons`, since it can be determined
  automatically from the other arguments.
*)

Arguments cons {_} {_} _ _.

(* Let's construct some `vector`s. *)

Check nil string. (* `vector string 0` *)
Check cons "foo" (nil string). (* `vector string 1` *)
Check cons "hello" (cons "world" (nil string)). (* `vector string 2` *)

(*
  Here's a function which produces an `vector` of a given length containing
  empty strings.
*)

Fixpoint emptyStrings n1 : vector string n1 :=
  match n1 with
  | O => nil string
  | S n2 => cons "" (emptyStrings n2)
  end.

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
  in vector _ n3
  return vector T (n3 + n2) (* Here, `n3` = `n1`. *)
  with
  | nil _ => v2 (* But `n3` = `0` here. *)
  | cons x v3 => cons x (concatenate v3 v2) (* And `n3` = `S (len v3)` here. *)
  end.

(*
  Here's a function which returns the first element of a `vector`. It's a type
  error to call this function on an empty `vector`.
*)

Definition head {T n} (v : vector T (S n)) : T :=
  match v with
  (* No need to handle the `nil` case! *)
  | cons x _ => x
  end.

Compute head (cons "hello" (nil string)).

(*
  The following doesn't type check:

  ```
  Compute head (nil string).
  ```
*)

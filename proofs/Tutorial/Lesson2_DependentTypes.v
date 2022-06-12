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
  return types as well. Such functions are called *type families*.
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
  depends on the argument. Note the use of the `return` keyword to annotate
  the return type, since it depends on `x`.
*)

Definition weird x :=
  match x return boolToSet x with
  | true => 42
  | false => "hello"
  end.

Check weird. (* `forall x : bool, boolToSet x` *)

Compute weird true. (* `42` *)

Compute weird false. (* `"hello"` *)

(**********************)
(* Inductive families *)
(**********************)

(*
  We saw in Lesson 1 that inductive data types can have type *parameters*.
  However, parameters don't need to be types, as demonstrated by the following
  contrived example:
*)

Inductive contrived (x : nat) :=
| contrivedFoo : contrived x
| contrivedBar : contrived x.

Check contrived. (* `nat -> Set` *)

Check contrivedFoo. (* `forall x : nat, contrived x` *)

Check contrivedBar. (* `forall x : nat, contrived x` *)

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

(*
  Indices are strictly more general than parameters. For example, we can define
  the `contrived` family with an index instead of a parameter:
*)

Inductive evenMoreContrived : nat -> Set :=
| evenMoreContrivedFoo : forall x, evenMoreContrived x
| evenMoreContrivedBar : forall x, evenMoreContrived x.

Check evenMoreContrived. (* `nat -> Set` *)

Check evenMoreContrivedFoo. (* `forall x : nat, evenMoreContrived x` *)

Check evenMoreContrivedBar. (* `forall x : nat, evenMoreContrived x` *)

(*
  The terminology is somewhat confusing. `contrived`, which has a parameter, is
  called a *family of inductive types*. `alsoContrived` and
  `evenMoreContrived`, which each have an index, are called
  *inductively defined families*, or *inductive families* for short. Families
  of inductive types, inductive families, and functions which return types are
  all called *type families*.
*)

(************************************)
(* Case study: length-indexed lists *)
(************************************)

(* Length-indexed lists of strings *)

Inductive slist : nat -> Type :=
| snil : slist O
| scons :
    forall {n}, (* Length of the tail, implicit due to the curly braces *)
    string ->   (* Head *)
    slist n ->  (* Tail *)
    slist (S n).

(* Let's construct some `slists`. *)

Check snil. (* `slist 0` *)
Check scons "foo" snil. (* `slist 1` *)
Check scons "hello" (scons "world" snil). (* `slist 2` *)

(*
  Here's a function which produces an `slist` of a given length containing
  empty strings.
*)

Fixpoint empty_strings n1 : slist n1 :=
  match n1 with
  | O => snil
  | S n2 => scons "" (empty_strings n2)
  end.

(*
  Here's a function which concatenates two `slists`. This demonstrates how to
  do dependent pattern matching.
*)

Fixpoint concat {n1 n2}
         (l1 : slist n1)
         (l2 : slist n2) :
         slist (n1 + n2) :=
  match l1 in slist n3
  return slist (n3 + n2) (* Here, `n3` = `n1`. *)
  with
  | snil => l2 (* But `n3` = `0` here. *)
  | scons x l3 => scons x (concat l3 l2) (* And `n3` = `S (len l3)` here. *)
  end.

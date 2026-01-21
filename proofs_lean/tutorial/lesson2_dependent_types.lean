/-============================================-/
/-============================================-/
/-===                                      ===-/
/-===   Programming with dependent types   ===-/
/-===                                      ===-/
/-============================================-/
/-============================================-/

/-===============-/
/- Type families -/
/-===============-/

/-
  In Lesson 1, we saw that functions can take types as arguments. Functions can
  return types as well. Functions that return types are called *type families*.
-/

def BoolToType x :=
  match x with
  | true => Nat
  | false => String

#check BoolToType -- `BoolToType (x : Bool) : Type`

-- Unfortunately `#eval` doesn't work on type expressions, so we use `#reduce`.
#reduce (types := true) BoolToType true -- `Nat`

#reduce (types := true) BoolToType false -- `String`

/-
  Lean considers types *definitionally equal* if they compute to syntactically
  identical types. This notion of equality between types is the one used for
  type checking. For example, we can give the value `42` the following two
  types which are definitionally equal:
-/

def age1 : Nat := 42

def age2 : BoolToType true := age1

/-
  Using `BoolToType`, we can construct a function for which the return type
  depends on the argument. Note the use of the `motive` syntax to specify how
  the type of the `match` expression depends on the value being matched on. In
  general, such an annotation is needed when the branches of a pattern match
  don't all have the same type.
-/

def weird x :=
  match (motive := forall x, BoolToType x) x with
  | true => age1
  | false => "hello"

-- In most cases, the motive can be given more succinctly by a type annotation:

def better_weird x : BoolToType x :=
  match x with
  | true => age1
  | false => "hello"

#check better_weird -- `better_weird (x : Bool) : BoolToType x`

#eval better_weird true -- `42`

#eval better_weird false -- `"hello"`

/-================================================-/
/- Parameters and indices of inductive data types -/
/-================================================-/

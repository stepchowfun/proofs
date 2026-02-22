/-===========================================-/
/-===========================================-/
/-===                                     ===-/
/-===   Ordinary functional programming   ===-/
/-===                                     ===-/
/-===========================================-/
/-===========================================-/

/-=========================-/
/- Variables and functions -/
/-=========================-/

/-
  Sometimes it's useful to ask Lean for the type of an expression. We can use
  the `#check` command for that. For example, the type of the expression below
  is `Nat`, which stands for "natural number". Natural numbers are unsigned
  integers, and they're the most common type of number in Lean.

  To use these commands interactively, be sure you're using the Lean extension
  for Visual Studio Code.
-/

#check 3 + 4 -- `Nat`

-- If we want Lean to actually evaluate an expression, we can use `#eval`.

#eval 3 + 4 -- `7`

/-
  We can define variables with the `def` keyword. Lean is able to infer that
  the type of this variable is `Nat`.
-/

def my_variable := 42

#check my_variable -- `Nat`

/-
  Functions are data too, so we can also use `def` to introduce functions. Lean
  is able to infer that the type of this function is `Nat → Nat` based the
  body.
-/

def parabola := fun x => 2 * x * x

-- For function definitions, `#check` prints the signature like this:

#check parabola -- `parabola (x : Nat) : Nat`

-- We can get the actual type by prepending the function name with `@`:

#check @parabola -- `Nat → Nat`

-- Here's a more convenient syntax for defining a function:

def better_parabola x := 2 * x * x

#check better_parabola -- `better_parabola (x : Nat) : Nat`

/-
  To call a function `f` on some input `x`, we simply write `f x`. Note that we
  don't need parentheses, unlike in other languages.
-/

#eval parabola my_variable -- `3528`

/-
  In Lean, every function takes exactly one argument. However, we can use
  "currying" to represent functions of multiple arguments as nested functions.
  Suppose we want to define a function of two arguments. We can write it as a
  function which takes only the first argument and returns another function
  which takes the second argument to the final result.
-/

def paraboloid := fun x => fun y => 2 * (x * x + y * y)

#check paraboloid -- `paraboloid (x y : Nat) : Nat`

/-
  As before, Lean is not printing the function's type per se, but something
  slightly more informative. The type itself is `Nat → Nat → Nat`, which should
  be understood as `Nat → (Nat → Nat)`, not `(Nat → Nat) → Nat`.

  Lean has a more convenient syntax for defining curried functions like this:
-/

def better_paraboloid x y := 2 * (x * x + y * y)

#check better_paraboloid -- `Nat → Nat → Nat`

/-
  To call a curried function `f` with two arguments `x` and `y`, write `f x y`.
  This should be understood as `(f x) y`, not `f (x y)`.
-/

#eval paraboloid 3 4 -- `50`

-- Currying works with any number of arguments.

def density x y z := 2 * x + y * z

#check density -- `density (x y z : Nat) : Nat`

#eval density 3 4 5 -- `26`

/-
  Sometimes, the type of a function's argument can't be inferred automatically.
  For example, if we try to define the identity function like this:

  ```
  def id_bad x := x
  ```

  Lean reports this error:

  ```
  Failed to infer type of definition `id_bad`
  Error code: lean.inferDefTypeFailed

  Failed to infer type of binder `x`
  Error code: lean.inferBinderTypeFailed
  ```

  To resolve this ambiguity, we need to provide a type annotation for `x`:
-/

def id_nat (x : Nat) := x

#check id_nat -- `id_nat (x : Nat) : Nat`

def id_bool (x : Bool) := x

#check id_bool -- `id_bool (x : Bool) : Bool`

/-
  Those identity functions are almost exactly the same, except they're defined
  on different types. Wouldn't it be nice to define a universal identity
  function that works on all types? It turns out that types are data, just like
  numbers and functions. So all we need to do is take the type as an extra
  argument. The type of that argument will be `Type`, which is the type of
  types like `Nat`, `Bool`, `Nat → Bool`, and so on. A type which has types as
  members is called a *universe*. Lesson 5 discusses universes in depth.

  The idea of parameterizing a definition by a type is known as "generics" in
  many languages, e.g., Java and Rust.
-/

def polymorphic_id (α : Type) (x : α) := x

#eval polymorphic_id Nat (3 + 4) -- `7`

/-
  What's the type of `polymorphic_id`? `polymorphic_id` is a curried function
  of two arguments, but the type of the second argument isn't fixed; it
  *depends* on the first argument, which isn't known here since it's provided
  by the caller. Thus, in the type of `polymorphic_id`, we need to give a name
  to the first argument (in this case, `α`) so we can refer to it in the type
  of the second argument.
-/

#check polymorphic_id -- `polymorphic_id (α : Type) (x : α) : α`

/-
  The actual type of `polymorphic_id` is `(α : Type) → α → α`.

  `α → β` is actually just shorthand for `(_ : α) → β`, where `_` is an
  inaccessible variable. We can write the type of `polymorphic_id` in any of
  the following equivalent ways:

  - `(α : Type) → α → α`
  - `∀ (α : Type), α → α`
  - `(α : Type) → (_ : α) → α`
  - `∀ (α : Type) (_ : α), α`

  For this type, the first or second styles are best, since they makes it clear
  that the return type doesn't depend on the value of the second argument.

  This identity function only works on types in the universe `Type` (i.e.,
  `Sort 1`), but there are other universes such as `Prop` (i.e., `Sort 0`),
  `Type 1` (i.e., `Sort 2`), `Type 2` (i.e., `Sort 3`), etc.:
-/

#check Prop -- `Type`
#check Type -- `Type 1`
#check Type 1 -- `Type 2`
#check Type 2 -- `Type 3`

/-
  We can generalize the identity function even further by making it work for
  any universe:
-/

def universe_polymorphic_id.{u} (α : Sort u) (x : α) := x

#eval universe_polymorphic_id Nat (3 + 4) -- `7`

-- `universe_polymorphic_id.{u} (α : Sort u) (x : α) : α`
#check universe_polymorphic_id

/-
  When using the `universe_polymorphic_id` function, Lean automatically figures
  out which universe level `u` to use. It would be nice if Lean could do the
  same for the type argument `α`. We can declare the argument *implicit* by
  using curly braces instead of parentheses. Then Lean will try to figure it
  out automatically whenever we use the function.
-/

def better_id.{u} {α : Sort u} (x : α) := x

#check better_id -- `better_id.{u} {α : Sort u} (x : α) : α`

#eval better_id (3 + 4) -- `7`

/-
  If Lean is unable to infer the implicit arguments, we can pass them
  explicitly by prefixing the function with `@`.
-/

#eval @better_id Nat (3 + 4) -- `7`

-- We can also do this:

#eval better_id (α := Nat) (3 + 4) -- `7`

/-=============================-/
/- Simple inductive data types -/
/-=============================-/

/-
  An *inductive data type* is defined by cases, called *constructors*. For
  example, we can define a type called `Bool` with two constructors: `true` and
  `false`. The standard library already defines this type, so we'll just show
  it here in this comment:

  ```
  inductive Bool where
  | true
  | false
  ```
-/

#check true -- `Bool`

#check false -- `Bool`

#check Bool -- `Type`

/-
  Constructors of an inductive type are namespaced by default, so ordinarily
  we'd have to write `Bool.true` and `Bool.false` instead of `true` and
  `false`, respectively. We can bring them into the current namespace with the
  `open` command.
-/

open Bool

/-
  We didn't have to do that though, since the standard library exports the
  constructors of `Bool` individually.

  To use a `Bool`, we can do case analysis on it. This is called *pattern
  matching*. For example, we can use pattern matching to define a function that
  inverts a `Bool`. Since that function is already in the standard library,
  here it is in a comment:

  ```
  def not b :=
    match b with
    | true => false
    | false => true
  ```
-/

#eval not true -- `false`

#eval not false -- `true`

/-
  Lean provides syntactic sugar for functions that do pattern matching:

  ```
  def better_not : Bool → Bool
  | true => false
  | false => true
  ```

  Each case of an inductive data type may store some data. In order to use that
  feature, we can provide a type annotation for each constructor describing
  what data that constructor accepts. For example, we can define a type such
  that its elements *might* hold a `Nat` as follows:
-/

inductive OptionNat where
| no_nat : OptionNat
| some_nat : Nat → OptionNat

/-
  We could also write it like this:

  ```
  inductive OptionNat where
  | no_nat
  | some_nat (val : Nat)
  ```
-/

#check OptionNat.no_nat -- `OptionNat`

#check OptionNat.some_nat -- `Nat → OptionNat`

#check OptionNat.some_nat 3 -- `OptionNat`

#check OptionNat -- `Type`

/-
  When pattern matching on an `OptionNat`, we get access to the `Nat` in the
  `some` case. Here's a function which will transform the `Nat`, if it exists,
  by a user-provided function. Note that instead of `OptionNat.no_nat` and
  `OptionNat.some_nat`, we can simply write `.no_nat` and `.some_nat` since the
  type annotations already tell Lean that these are from `OptionNat`.
-/

def map_option_nat (f : Nat → Nat) (o : OptionNat) : OptionNat :=
  match o with
  | .no_nat => .no_nat
  | .some_nat n => .some_nat (f n)

-- `map_option_nat (f : Nat → Nat) (o : OptionNat) : OptionNat`
#check map_option_nat

#eval map_option_nat parabola (OptionNat.some_nat 3) -- `OptionNat.some_nat 18`

#eval map_option_nat parabola OptionNat.no_nat -- `OptionNat.no_nat`

/-
  `OptionNat` only works with `Nat`s. We can add a type *parameter* to make it
  work for any type. This results in a family of inductive data types, one for
  every choice of `α`. Note that each constructor returns an `Option α`, rather
  than just an `Option`.

  ```
  inductive Option.{u} (α : Type u) where
  | none : Option α
  | some (val : α) : Option α
  ```

  Each constructor automatically takes the parameter as an implicit argument.
  Thus, if we check the type of each constructor, we find it doesn't exactly
  match the type we provided in the definition.
-/

#check none -- `Option.none.{u} {α : Type u} : Option α`

#check @none Bool -- `Option Bool`

#check some -- `Option.some.{u} {α : Type u} (val : α) : Option α`

#check @some Bool true -- `Option Bool`

#check Option -- `Option.{u} (α : Type u) : Type u`

/-
  When pattern matching, the implicit arguments to the constructors are not
  bound by default.
-/

def map_option.{u, v} {α : Type u} {β : Type v}
  (f : α → β) (o : Option α)
:=
  match o with
  | none => @none β
  | some x => some (f x)

/-
  Implicit arguments can be bound to variables using `@`. Parameters such as
  `α`, however, must be bound to inaccessible variables (`_`).

  ```
  def map_option.{u, v} {α : Type u} {β : Type v}
    (f : α → β) (o : Option α)
  :=
    match o with
    | @none _ => @none β
    | @some _ x => some (f x)
  ```
-/

/-
  ```
  map_option.{u, v} {α : Type u} {β : Type v} (f : α → β) (o : Option α)
    : Option β
  ```
-/
#check map_option

#eval map_option not none -- `none`

#eval map_option not (some false) -- `some true`

/-
  Inductive data types can be recursive. For example, below is how natural
  numbers are defined in the standard library:

  ```
  inductive Nat where
  | zero : Nat -- Zero
  | succ (n : Nat) : Nat -- Successor of another `Nat`
  ```
-/

#check Nat -- `Type`
#check Nat.zero -- `Nat`
#check Nat.succ -- `Nat.succ (n : Nat) : Nat`
#check Nat.succ Nat.zero -- `Nat`
#check Nat.succ (Nat.succ Nat.zero) -- `Nat`
#check Nat.succ (Nat.succ (Nat.succ Nat.zero)) -- `Nat`

-- Addition can be defined recursively.

def add (n m : Nat) :=
  match m with
  | .zero => n
  | .succ p => .succ (add n p)

/-
  Let's compute 1 + 1. In Lean, we can use numeric literals like `2` rather
  than writing `Nat.succ (Nat.succ Nat.zero)`.
-/

#eval add 1 1 -- `2`

/-
  The standard library also defines the `+` operator for addition, so we can
  simply write:
-/

#eval 1 + 1 -- `2`

/-===========-/
/- Exercises -/
/-===========-/

/-
  1. Define the concept of lists as an inductive data type which is
     parameterized by the element type.
  2. Define a function which computes the length of a list as defined in the
     previous question.
  3. Define a `map` function for lists as defined in the first question,
     analogous to the `map_option` function defined in the lesson.
  4. Define a function which compares two natural numbers for equality.
  5. Define multiplication of natural numbers.
  6. Define subtraction of natural numbers. The function should return an
     `Option Nat` to account for the fact that negative results can't be
     represented as natural numbers.
-/

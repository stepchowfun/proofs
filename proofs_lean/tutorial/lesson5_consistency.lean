/-===========================================================================-/
/-===========================================================================-/
/-===                                                                     ===-/
/-===   Restrictions imposed by Lean to ensure consistency of the logic   ===-/
/-===                                                                     ===-/
/-===========================================================================-/
/-===========================================================================-/

/-======================================================-/
/- All functions must be statically known to terminate. -/
/-======================================================-/

/-
  Lean rejects all nonterminating functions, such as:

  ```
  theorem f (n : Nat) : False := f n
  ```

  ```
  fail to show termination for
    f
  with errors
  failed to infer structural recursion:
  Not considering parameter n of f:
    it is unchanged in the recursive calls
  no parameters suitable for structural recursion

  well-founded recursion cannot be used, `f` does not take any (non-fixed)
  arguments
  ```

  If we were allowed to write that function, we could use it to prove `False`:

  ```
  theorem paradox : False := f 0
  ```

  To prevent this, Lean requires that recursive functions have some argument
  which is structurally "decreasing" at every recursive call. Lean can
  automatically figure out which argument that is.
-/

/-==================================================-/
/- A brief summary of the universe behavior in Lean -/
/-==================================================-/

/-
  Consider a type, such as `Nat`. What is its type? Suppose we call it `Type`,
  so `Nat : Type`. Then what is the type of `Type`?

  One might guess that `Type` is its own type, i.e., `Type : Type`. However, in
  a rather convoluted way, this would allow one to define a nonterminating
  function and prove `False`. This is called Girard's paradox, and you can find
  it in this repo at [file:proofs_rocq/type_theory/girard.v].

  So, instead of having `Type : Type`, we have an infinite hierarchy of
  universes `Sort i` for all `i` >= 0. `Sort 0` is also known as `Prop`,
  `Sort (i + 1)` is also known as `Type i`, and `Type 0` is also known as
  `Type`. All of the `Type i` universes are "predicative", which will be
  explained below. `Prop`, however, is an "impredicative" universe.
-/

-- If `A, B : Type i`, then `A → B : Type i`. This is called *predicativity*.

#check Bool → Nat -- `Type` (a.k.a. `Type 0` a.k.a. `Sort 1`)
#check Type → Type -- `Type 1` (a.k.a. `Sort 2`)
#check Prop → Type -- `Type 1` (a.k.a. `Sort 2`)

/-
  If `A` and `B` are in different universes, the function type lives in the
  higher universe.
-/

#check Type → Nat -- `Type 1`

-- If `B : Prop`, then `A → B : Prop`. This is called *impredicativity*.

#check Nat → True -- `Prop`
#check Type → True -- `Prop`
#check Prop → True -- `Prop`

-- Here are some identity functions for different universes:

def idProp (T : Prop) (x : T) := x
def idType (T : Type) (x : T) := x

-- Because `Prop` is impredicative, we can apply `idProp` to itself.

-- `idProp (∀ (T : Prop), T → T) idProp : ∀ (T : Prop), T → T`
#check idProp (∀ T : Prop, T → T) idProp

/-
  But `Type` is predicative, so we can't apply `idType` to itself:

  ```
  #check idType (∀ T : Type, T → T) idType
  ```

  ```
  Application type mismatch: The argument
    (T : Type) → T → T
  has type
    Type 1
  of sort `Type 2` but is expected to have type
    Type
  of sort `Type 1` in the application
    idType ((T : Type) → T → T)
  ```

  We saw in Lesson 1 that we can create definitions that are polymorphic over
  universes, like so:
-/

def idUniversal.{u} (T : Sort u) (x : T) := x

#check idUniversal -- `idUniversal.{u} (T : Sort u) (x : T) : T`

-- At first glance, it seems as though we can apply it to itself:

#check idUniversal _ idUniversal

/-
  But we're actually applying one version of it to another version of it in a
  lower universe. It fails if we force the two universes to be the same:

  ```
  def bad.{u} := idUniversal.{u} (∀ T : Sort u, T → T) idUniversal.{u}
  ```

  ```
  Application type mismatch: The argument
    (T : Sort u) → T → T
  has type
    Sort (imax (u + 1) u)
  of sort `Type (imax (u + 1) u)` but is expected to have type
    Sort u
  of sort `Type u` in the application
    idUniversal ((T : Sort u) → T → T)
  ```
-/

/-===============================-/
/- Universes and inductive types -/
/-===============================-/

/-
  If an inductive type in `Type i` has a constructor which takes an argument of
  type `T` in universe `Type j`, `i` must be at least as large as `j`.
  Parameter arguments are not considered.
-/

inductive Foo1 : Type where
| make_foo1 : Nat → Foo1

/-
  ```
  inductive Foo2 : Type where
  | make_foo2 : Type → Foo2
  ```

  ```
  Invalid universe level in constructor `Foo2.make_foo2`: Parameter has type
    Type
  at universe level
    2
  which is not less than or equal to the inductive type's resulting universe
  level
    1
  ```
-/

inductive Foo3 : Type 1 where
| make_foo3 : Type → Foo3

-- This restriction doesn't apply to inductive types in `Prop`.

inductive Foo4 : Prop where
| make_foo4 : Type → Foo4

/-
  There are no constraints between the universe of an inductive type and the
  universes of its parameters.
-/

inductive Foo5 (T : Type 1) : Type where
| make_foo5 : Foo5 T

inductive Foo6 (T : Type 1) : Prop where
| make_foo6 : Foo6 T

/-
  There are no constraints between the universe of an inductive type and the
  universes of its indices.
-/

inductive Foo7 : Type 1 → Type where
| make_foo7 : Foo7 Type

inductive Foo8 : Type 1 → Prop where
| make_foo8 : Foo8 Type

/-=========================================================-/
/- Inductive types have a "strict positivity requirement". -/
/-=========================================================-/

-- The following type is allowed, even though it has no inhabitants.

inductive Weird where
| make_weird : Weird → Weird

example : Weird -> False := by
  intro h
  induction h
  assumption

-- This "reflexive" type is also allowed:

inductive Weirder where
| make_weirder : (Nat → Weirder) → Weirder

example : Weirder → False := by
  intro h
  induction h with
  | make_weirder _ h =>
    apply h
    exact 0

/-
  However, the following is not allowed:

  ```
  inductive Bad where
  | make_bad : (Bad -> Nat) -> Bad
  ```

  ```
  (kernel) arg #1 of 'Bad.make_bad' has a non positive occurrence of the
  datatypes being declared
  ```

  Why does Lean reject `Bad`? Suppose it were allowed. Consider the following
  function:

  ```
  def evil (x : Bad) : Nat :=
    match x with
    | .make_bad f => f x
  ```

  We could use `evil` to construct the following diverging term:

  ```
  def catastrophe : Nat := evil (Bad.make_bad evil)
  ```

  This is also rejected:

  ```
  inductive AlsoBad :=
  | make_also_bad : ((AlsoBad -> Nat) -> Nat) -> AlsoBad
  ```

  `AlsoBad` could be used to construct a diverging function in an impredicative
  universe, as demonstrated in this paper:

    Coquand, T., Paulin, C. (1990). Inductively defined types. In: Martin-
    Löf, P., Mints, G. (eds) COLOG-88. COLOG 1988. Lecture Notes in Computer
    Science, vol 417. Springer, Berlin, Heidelberg.
    https://doi.org/10.1007/3-540-52335-9_47

  `AlsoBad` is not known to cause any theoretical issues in predicative
  universes, but Lean still rejects it regardless of the universe in which it's
  defined.
-/

/-===========-/
/- Exercises -/
/-===========-/

/-
  1. Explain why Lean requires that all functions terminate on all inputs. How
     does Lean enforce this?
  2. Describe impredicativity. Does `Type i` have it? Does `Prop` have it?
  3. Describe the restrictions Lean imposes on inductive data types.
-/

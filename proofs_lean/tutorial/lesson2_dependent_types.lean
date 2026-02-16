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

/-
  Unfortunately `#eval` doesn't work on type expressions, so we use `#reduce`
  with `(types := true)`.
-/
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
  depends on the argument. Note the use of the type annotation to specify how
  the type of the `match` expression depends on the value being matched on.
  Such an annotation is often needed when the branches of a pattern match don't
  all have the same type.
-/

def weird x : BoolToType x :=
  match x with
  | true => age1
  | false => "hello"

#check weird -- `weird (x : Bool) : BoolToType x`

#eval weird true -- `42`

#eval weird false -- `"hello"`

/-
  When pattern matching on `x`, Lean replaces `x` with `true` in the result
  type of the first branch (so the expected type is `BoolToType true`, i.e.,
  `Nat`) and with `false` in the result type of the second branch (so the
  expected type is `BoolToType false`, i.e., `String`).
-/

/-================================================-/
/- Parameters and indices of inductive data types -/
/-================================================-/

/-
  We saw in Lesson 1 that inductive data types can have *parameters*.
  Parameters give us a second way to define type families.

  ```
  inductive Option.{u} (α : Type u) where
  | none : Option α
  | some (val : α) : Option α
  ```
-/

#check Option -- Option.{u} (α : Type u) : Type u

/-
  A third way to define type families is to use *indices*. Indices are like
  parameters, but they unlock a new power: each constructor specifies a
  particular value for the index. Consider this example:
-/

inductive BoolOrNat : Type → Type where
| some_bool : Bool → BoolOrNat Bool
| some_nat : Nat → BoolOrNat Nat

#check BoolOrNat /- `Type → Type` -/

#check BoolOrNat.some_bool /- `Bool → BoolOrNat Bool` -/

#check BoolOrNat.some_nat /- `Nat → BoolOrNat Nat` -/

/-
  When pattern matching, the return type can depend on the indices (in this
  case, `T`) as well as the value being matched on (in this case, `x`).
-/

def pluck {T : Type} (x : BoolOrNat T) : T :=
  match T, x with
  | _, .some_bool b => b
  | _, .some_nat n => n

#eval pluck (BoolOrNat.some_bool true) -- `true`

/-
  As before, Lean refines the expected type in each branch. In the first
  branch, the expected type `T` becomes `Bool`, and it becomes `Nat` in the
  second branch.

  If we don't explicitly match on the index `T`, Lean will automatically do it
  for us.
-/

def simpler_pluck {T : Type} (x : BoolOrNat T) : T :=
  match x with
  | .some_bool b => b
  | .some_nat n => n

-- Let's see what Lean did with that definition:

#print simpler_pluck

#eval simpler_pluck (BoolOrNat.some_bool true) -- `true`

/-
  ```
  def simpler_pluck : {T : Type} → BoolOrNat T → T :=
    fun {T} x ↦
      match T, x with
      | .(Bool), BoolOrNat.some_bool b => b
      | .(Nat), BoolOrNat.some_nat n => n
  ```

  Lean's pattern matching is a bit magical. It refines the result type by
  replacing *all* occurrences of the expressions being matched, but in some
  situations we may need more control over which occurrences are replaced. We
  can specify how the result type varies depending on the inputs being matched
  by providing an explicit `motive`:
-/

def pluck_with_motive {T : Type} (x : BoolOrNat T) : T :=
  match (motive := (T : Type) -> (x : BoolOrNat T) -> T) T, x with
  | _, .some_bool b => b
  | _, .some_nat n => n

/-
  There's another way in which Lean's pattern matching is magical. If the
  expression being matched is a variable, Lean also refines the types of any
  variables in the context. Lean calls that "generalization", and it can be
  disabled as follows:
-/

def pluck_without_generalization {T : Type} (x : BoolOrNat T) : T :=
  match (generalizing := false) T, x with
  | _, .some_bool b => b
  | _, .some_nat n => n

/-
  To be fully explicit, we can also use the *recursor* for the type instead of
  pattern matching syntax. The recursor takes an argument called `motive` which
  is like the motive described above, except it's a type family rather than a
  dependent function type.
-/

#check BoolOrNat.rec

/-
  ```
  BoolOrNat.rec.{u}
    {motive : (a : Type) → BoolOrNat a → Sort u}
    (some_bool : (a : Bool) → motive Bool (BoolOrNat.some_bool a))
    (some_nat : (a : Nat) → motive Nat (BoolOrNat.some_nat a))
    {a✝ : Type}
    (t : BoolOrNat a✝)
  : motive a✝ t
  ```

  When we use a recursor, Lean requires that we mark the definition as
  `noncomputable` since the code generator doesn't know what to do with the
  recursor. We also need to use `#reduce` instead of `#eval` for the same
  reason.
-/

noncomputable def pluck_the_explicit_way {T : Type} (x : BoolOrNat T) : T :=
  @BoolOrNat.rec (fun T _ => T) (fun b => b) (fun n => n) T x

#reduce pluck_the_explicit_way (BoolOrNat.some_bool true) -- `true`

/-
  The terminology is somewhat confusing. `Option` is called a *family of
  inductive types*. `BoolOrNat` is called an *inductively defined family*, or
  *inductive family* for short. Families of inductive types, inductive
  families, and functions which return types are all called *type families*.
-/

/-==================================-/
/- Case study: length-indexed lists -/
/-==================================-/

/-
  Putting all this together, we're going to define a type which features both
  a parameter and an index. This type represents lists. The parameter indicates
  the type of the elements. The index indicates the length of the list. Lists
  which feature their length in their type are called *vectors*:
-/

inductive Vec (T : Type) : Nat → Type where
| empty : Vec T 0
| nonempty : forall {n}, T → Vec T n → Vec T (n + 1)

/- Let's construct some `Vec`s. -/

-- `Vec Bool 0`
#check @Vec.empty Bool

-- `Vec Bool (0 + 1)` (i.e., `Vec Bool 1`)
#check Vec.nonempty true Vec.empty

-- `Vec Bool (0 + 1 + 1)` (i.e., `Vec Bool 2`)
#check Vec.nonempty false (Vec.nonempty true Vec.empty)

-- Here's a function which produces a `Vec` of zeros of a given length.

def zeroes n1 :=
  match n1 with
  | Nat.zero => @Vec.empty Nat
  | Nat.succ n2 => Vec.nonempty 0 (zeroes n2)

-- `zeroes (n1 : Nat) : Vec Nat n1`
#check zeroes

-- `Vec.nonempty 0 (Vec.nonempty 0 (Vec.nonempty 0 (Vec.empty)))`
#eval zeroes 3

-- Here's a function which concatenates two `Vec`s.

def concatenate
           {T n1 n2}
           (v1 : Vec T n1)
           (v2 : Vec T n2) :
           Vec T (n2 + n1) :=
  match v1 with
  | .empty => v2
  | .nonempty x v3 => Vec.nonempty x (concatenate v3 v2)

/-
  Here's a function which returns the first element of a `Vec`. It's a type
  error to call this function on an empty `Vec`.
-/

def head {T n} (v : Vec T (Nat.succ n)) : T :=
  match v with
  | .nonempty x _ => x

/-
  You might have noticed we didn't handle the `empty` case! What's going on
  here?
-/

#reduce head

/-
  ```
  fun v ↦
    Vec.rec
      (motive := fun a x ↦
        Nat.succ ?m.2 = a → v ≍ x → (fun v ↦ ?m.1) v)
      (fun h ↦
        False.rec (fun x ↦ v ≍ Vec.empty → (fun v ↦ ?m.1) v) ⋯)
      (fun {n} a a_1 a_ih h ↦
        (⋯ ▸ fun a_2 h ↦ ⋯ ▸ a) a_1)
      v ⋯ ⋯
  ```

  Lean is smart enough to know the `empty` case is impossible, so it handles it
  automatically for us. As we can see, the way Lean does it is a bit
  complicated, but we can show how to do it in a simpler way:
-/

def head_explicit {T n} (v : Vec T (Nat.succ n)) : T
:= (
  match Nat.succ n, v with
  | _, .empty => Unit.unit
  | _, .nonempty x _ => x
  : match Nat.succ n with
    | .zero => Unit
    | .succ _ => T
)

-- Let's try it out on a simple example.

#eval head (Vec.nonempty true Vec.empty) -- `true`

#eval head_explicit (Vec.nonempty true Vec.empty) -- `true`

/-
  By design, we can't take the `head` of an empty vector. If we try this:

  ```
  #eval head (@Vec.empty Bool)
  ```

  Lean gives the following error:

  ```
  Application type mismatch: The argument
    Vec.empty
  has type
    Vec Bool 0
  but is expected to have type
    Vec ?m.2 (Nat.succ ?m.3)
  in the application
    head Vec.empty
  ```
-/

/-====================-/
/- The convoy pattern -/
/-====================-/

-- Suppose we have a number `n`.

axiom n : Nat

/-
  The following variable `x` has an interesting type. When `n` is even, `x` is
  a `Nat`. Conversely, when `n` is odd, `x` is a `String`. However, the parity
  of `n` is unknown here, so `x` seems to have some kind of superposition of
  types.
-/

axiom x : BoolToType (n % 2 == 0)

/-
  Suppose we want to do something with `x`. Since the type of `x` depends on
  whether `n` is even or odd, we should expect to handle those two cases
  separately. For example, if `n` is even, we might want to do some arithmetic
  with `x`, since it's a `Nat` in that case. Otherwise, `x` is a `String`, and
  perhaps we wish to compute its length. Unfortunately, we can't do that by
  naively pattern matching on the parity of `n`. If we try this:

  ```
  #check
    match n % 2 == 0 with
    | true => x + 1
    | false => x.length
  ```

  Lean gives this error for the first case:

  ```
  failed to synthesize
  HAdd (BoolToType (n % 2 == 0)) Nat ?m.12
  ```

  And this error for the second:

  ```
  Invalid field `length`: The environment does not contain
  `BoolToType.match_1.length`
    x
  has type
    match n % 2 == 0 with
    | true => Nat
    | false => String
  ```

  The issue is that Lean doesn't refine the type of `x` based on the knowledge
  gained about the parity of `n` in each case. To make the example work, we can
  use the *convoy pattern*. First, we use dependent pattern matching to
  construct a function which accepts an arbitrary `BoolToType (n % 2 == 0)`,
  then we immediately call that function on `x`. Dependent pattern matching
  refines the type of the result on each case, so each branch only needs to
  consider the specific value of `n % 2 == 0` (`true` or `false`) corresponding
  to that case.
-/

#check
  (
    match n % 2 == 0 with
    -- `@id Nat` forces Lean to reduce the type of `y` from `BoolToType true`
    -- to `Nat`, which is needed for type class instance resolution for `+` to
    -- work.
    | true => fun y => @id Nat y + 1
    | false => fun y => y.length
    : BoolToType (n % 2 == 0) -> Nat
  ) x

/-===========-/
/- Exercises -/
/-===========-/

/-
  1. Explain the differences between parameters and indices. When should you
     use one over the other?
  2. When pattern matching, how can the expected type vary from branch to
     branch?
  3. Define a `tail` function which takes a `Vec` and returns a new `Vec` with
     the contents of the original `Vec` but without the head. It should work
     with any `Vec` as its input, including the empty `Vec`.
  4. What is the convoy pattern, and when is it needed?
-/

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
  When pattern matching on `x`, Lean replaces `x` with `true` in the expected
  type of the first branch (so the expected type is `BoolToType true`, i.e.,
  `Nat`) and with `false` in the expected type of the second branch (so the
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
  As before, Lean replaces any occurrences of the expressions being matched on
  in the expected type with the appropriate values in each branch. In the first
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

  Lean's pattern matching is a bit magical. It replaces *all* occurrences of
  the expressions being matched in the expected type, but in some situations
  you may want more control over which occurrences are replaced. To be fully
  explicit, we can use the *recursor* for the type instead of pattern matching
  syntax.
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
  recursor.
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
  Here's a function which returns the first element of a `Vector`. It's a type
  error to call this function on an empty `Vector`.
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
  automatically with a dummy value . The dummy value doesn't have the same type
  as the `nonempty` case, so this is a dependent pattern match.

  Let's try it out on a simple example.
-/

#eval head (Vec.nonempty true Vec.empty) -- `true`

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
-/

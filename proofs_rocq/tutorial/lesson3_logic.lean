/-==========================-/
/-==========================-/
/-===                    ===-/
/-===   Writing proofs   ===-/
/-===                    ===-/
/-==========================-/
/-==========================-/

/-
  Consider a mathematical statement, i.e., a *proposition*, that you'd like to
  prove. An example of a proposition is that addition of natural numbers is
  commutative. In Lean, we'd represent that proposition as a type:

  ```
  ∀ x y, x + y = y + x
  ```

  This type might seem strange at first. You already know about `∀` and `+`,
  but we haven't seen `=` yet. Fear not! In this lesson, we'll see how this
  notion of equality and other logical constructs like "and" and "or" can be
  defined as type families in Lean.

  How then can we prove a proposition like that? In Lean, we prove a
  proposition by constructing an element of the corresponding type. So a proof
  corresponds to a program, and the proposition it proves corresponds to the
  type of that program. This idea is called *propositions as types*.

  It'll be useful to define a proposition which is trivially true. We'll call
  this proposition `True`, but don't mistake it for a `Bool`! As explained
  above, propositions like `True` correspond to types.

  ```
  inductive True : Prop where
  | intro : True
  ```
-/

#check True.intro -- `True`

/-
  So `True` is a proposition, and `True.intro` is its proof. That's a bit
  abstract, but it'll become more clear once we define a few other logical
  concepts.

  Note that `True` is defined in a universe called `Prop` instead of `Type`. In
  general, propositions will live in `Prop`. This is an easy way to distinguish
  proofs from programs, and it'll allow Lean to erase all the proofs when
  compiling the code. See Lesson 5 for details about universes.

  Along the same lines as `True`, it'll also be useful to have a proposition
  which is trivially false:

  ```
  inductive False : Prop
  ```

  Note that `False` has no constructors and therefore no proofs!

  We don't need to define *implication*, since "A implies B" is just `A → B`.
  In other words, a proof of "A implies B" is a function which transforms a
  proof of "A" into a proof of "B".
-/

theorem modus_ponens (A B : Prop) : (A → B) → A → B :=
  fun h1 h2 => h1 h2

example : ∀ A B : Prop, (A → B) → A → B := by
  intro _ _ h1 _ -- `intro` moves premises of the goal into the context.
  apply h1
  assumption -- `assumption` looks for a proof of the goal in the context.

/-
  One of the most familiar logical concepts is *conjunction*, also known as
  "and". To prove "A and B", we need to provide a proof of "A" and a proof of
  "B". We can define this in Lean as follows:

  ```
  structure And (a b : Prop) : Prop where
    intro ::
    left : a
    right : b
  ```

  The following specifies that the notation `A ∧ B` will be used as shorthand
  for `And A B`.

  ```
  infixr:35 " ∧ " => And
  ```

  You can look up a notation as follows:
-/

set_option pp.notation false in
#check True ∧ True -- `And True True : Prop`

-- Let's write a proof!

theorem true_and_true_1 : True ∧ True := And.intro True.intro True.intro

/-
  Writing proofs by hand can be extremely tedious in practice. Lean has a
  tactic language to help us construct proofs. We can use tactics in *tactic
  mode*. Below is the same proof as above, but written using tactic mode.

  To write proofs using tactic mode, it's essential that you're using an IDE
  that supports Lean, such as Visual Studio Code with the Lean extension.

  We use `theorem` when we want to give a name to the proof (e.g., to use it in
  a later proof) and `example` if the proof doesn't need a name.
-/

theorem true_and_true_2 : True ∧ True := by
  /-
    Use `apply` to prove the goal via some known fact. In this case, we'll use
    the fact that we can prove a conjunction by proving each half individually.
  -/
  apply And.intro
  . apply True.intro -- We can use `apply` again to solve this subgoal.
  . apply True.intro -- Déjà vu!

#print true_and_true_2 -- `⟨True.intro, True.intro⟩`

/-
  The `⟨x, y, ...⟩` notation works when the constructor (in this case,
  `And.intro`) is known from context.

  The proof above had two subgoals, and both were solved by `apply True.intro`.
  In situations like that, we can use the `<;>` *combinator* to reduce
  duplication:
-/

theorem true_and_true_3 : True ∧ True := by
  apply And.intro <;> apply True.intro

#print true_and_true_3 -- `⟨True.intro, True.intro⟩`

/-
  We get stuck if we try to prove `True ∧ False`:

  ```
  example : True ∧ False := by
    apply And.intro
    . apply True.intro
    . ??? -- No way to prove `False`
  ```
-/

theorem conjunction_symmetric A B : A ∧ B → B ∧ A :=
  fun h1 =>
    match h1 with
    | .intro h2 h3 => ⟨h3, h2⟩

example : ∀ A B : Prop, A ∧ B → B ∧ A := by
  intro _ _ h1

  /-
    `cases` does pattern matching. We can use it to destruct a proof of `A ∧ B`
    to get access to the proofs of `A` and `B`.
  -/
  cases h1
  constructor <;> assumption -- `constructor` applies the relevant constructor.

/-
  To prove the *disjunction* "A or B", we must provide either a proof of "A" or
  a proof of "B".

  ```
  inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b

  infixr:30 " ∨ " => Or
  ```
-/

theorem disjunction_symmetric A B : (A ∨ B) → (B ∨ A) :=
  fun h1 =>
    match h1 with
    | .inl h2 => .inr h2
    | .inr h2 => .inl h2

example : ∀ A B, (A ∨ B) → (B ∨ A) := by
  intro _ _ h
  cases h -- This generates a subgoal for each case.
  . right -- We could also use `apply Or.inr`.
    assumption
  . left -- We could also use `apply Or.inl`.
    assumption

/-
  To prove the *equivalence* "A if and only if B", we have to prove "A" and "B"
  imply each other.

  ```
  structure Iff (a b : Prop) : Prop where
    intro ::
    mp : a → b
    mpr : b → a

  infix:20 " ↔ " => Iff
  ```
-/

theorem iff_symmetric A B : (A ↔ B) → (B ↔ A) :=
  fun h => Iff.intro h.mpr h.mp

example : ∀ A B, (A ↔ B) → (B ↔ A) := by
  intro _ _ h
  cases h
  apply Iff.intro <;> assumption

/-
  In Lean, the *negation* "not A" is defined as "A implies False".

  ```
  def Not (a : Prop) : Prop := a → False

  notation:max "¬" p:40 => Not p
  ```
-/

#print not_false -- `theorem not_false : ¬False := id`

example : ¬False := by
  unfold Not -- `unfold` replaces a name with its definition.
  intro _
  assumption

theorem explosion (A : Prop) : False → A :=
  fun h =>
    nomatch h -- No cases to worry about!

#check explosion -- `explosion (A : Prop) : False → A`

example : ∀ A : Prop, False → A := by
  intro _ h
  cases h

/-
  In Lesson 2, we learned that Lean has a built-in notion of equality which is
  used for type checking: two expressions are considered equal if they compute
  to syntactically identical expressions. This is definitional equality.

  Thus, `n + 0` is definitionally equal to `n`, because `+` pattern matches on
  the `0` and returns `n` in that case. However, `0 + n` is not definitionally
  equal to `n`. How unfortunate!

  We can define a more flexible version of equality as an inductive family.
  This kind of equality isn't as convenient to work with, since the type
  checker can't use it automatically by doing computation. However, it allows
  us to *prove* that `0 + n = n`, and then we can use such a proof to freely
  substitute one side for the other. This notion of equality which requires
  proof is called *propositional equality*:

  ```
  inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a

  infix:50 " = " => Eq

  def Ne {α : Sort u} (a b : α) := ¬(a = b)

  infix:50 " ≠ " => Ne
  ```
-/

theorem one_plus_one_equals_two : 1 + 1 = 2 := Eq.refl 2

example : 1 + 1 = 2 := by rfl -- Equivalent to `apply Eq.refl`

theorem eq_symmetric A (x y : A) : x = y → y = x :=
  fun h =>
    match h with
    | Eq.refl _ => Eq.refl x

example : ∀ A (x y : A), x = y → y = x := by
  intro _ _ _ h
  rw [h] -- Replace `x` with `y` in the goal (and solve it).

example : ∀ A (x y : A), x = y → y = x := by
  intro _ _ _ h
  rw [← h] -- Replace `y` with `x` in the goal (and solve it).

example : ∀ A (x y : A), x = y → y = x := by
  intro _ _ _ _
  symm -- Turn `y = x` into `x = y` in the goal.
  assumption

example : ∀ A (x y : A), x = y → y = x := by
  intro _ _ _ h
  symm at h -- Turn `y = x` into `x = y` in hypothesis `h`.
  assumption

theorem eq_transitive A (x y z : A) : x = y → y = z → x = z :=
  fun h1 h2 =>
    match h2 with
    | .refl _ => h1

example : ∀ A (x y z : A), x = y → y = z → x = z := by
  intro _ _ _ _ h1 h2
  rw [h1, h2]

example : ∀ A (x y z : A), x = y → y = z → x = z := by
  intro _ _ _ _ h1 h2
  rw [← h2, ← h1]

example : ∀ A (x y z : A), x = y → y = z → x = z := by
  intro _ _ _ _ h1 h2
  rw [h2] at h1 -- Replace `y` with `z` in hypothesis `h1`.
  assumption

example : ∀ A (x y z : A), x = y → y = z → x = z := by
  intro _ _ _ _ h1 h2
  rw [← h1] at h2 -- Replace `y` with `x` in hypothesis `h2`.
  assumption

/-
  *Universal quantification* corresponds to the built-in `∀` syntax. Thus, we
  don't need to define it explicitly.
-/

theorem not_involution (b : Bool) : not (not b) = b :=
  match b with
  | true => .refl true
  | false => .refl false

#check not_involution -- `not_involution (b : Bool) : (!!b) = b`

example : ∀ b, not (not b) = b := by
  intro b
  cases b <;> rfl

theorem weird (f : Nat → Nat) :
  (∀ x, f x = x + 1) →
  ∀ x, f x + 1 = x + 2
:=
  fun h1 x =>
    match (motive := ∀ z, f x = z → f x + 1 = z + 1) x + 1, h1 x with
    | _, .refl _ => .refl _

example :
  ∀ f : Nat → Nat,
  (∀ x, f x = x + 1) →
  ∀ x, f x + 1 = x + 2 :=
by
  intro _ h _
  rw [h]

/-
  *Existential quantification* can be defined as follows:

  ```
  inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p
  ```

  There's a macro for this type which allows you to write `∃ x, P x` instead of
  `Exists P`.
-/

theorem half_of_6_exists : ∃ x, 2 * x = 6 :=
  ⟨3, Eq.refl 6⟩ -- Equivalent to `Exists.intro 3 (Eq.refl 6)`

example : ∃ x, 2 * x = 6 := by
  exists 3 -- Equivalent to `apply Exists.intro 3; trivial`

theorem divisible_by_4_implies_even x : (∃ y, 4 * y = x) → (∃ z, 2 * z = x) :=
  fun ⟨y, h2⟩ =>
    ⟨
      2 * y,
      match
        (motive := ∀ z, ((2 * 2) * y = z) → z = x)
        _, Nat.mul_assoc 2 2 y
      with
      | _, .refl _ => h2
    ⟩

example : ∀ x, (∃ y, 4 * y = x) → (∃ z, 2 * z = x) := by
  intro _ ⟨y, h⟩
  exists 2 * y
  rw [← Nat.mul_assoc 2 2 y]
  assumption

/-===========-/
/- Exercises -/
/-===========-/

/-
  1. Prove `∀ (A B C : Prop), (A → B) → (A → C) → A → B ∧ C` both manually and
     using tactic mode.
  2. Prove `∀ (A B : Prop), (A ∧ B) → (A ∨ B)` both manually and using tactic
     mode.
  3. Prove `∀ A : Prop, ¬(A ∧ ¬A)` both manually and using tactic mode.
  4. Prove `∀ A : Prop, ¬¬¬A → ¬A` both manually and using tactic mode.
  5. Prove `∀ x, x = 0 ∨ ∃ y, y + 1 = x` both manually and using tactic mode.
-/

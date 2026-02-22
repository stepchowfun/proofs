/-============================-/
/-============================-/
/-===                      ===-/
/-===   Proof techniques   ===-/
/-===                      ===-/
/-============================-/
/-============================-/

/-==========================-/
/- Equality of applications -/
/-==========================-/

/-
  To prove two applications of a function or constructor are equal, we can
  prove the arguments are pairwise equal.
-/

theorem successors_equal n1 n2 : n1 = n2 → Nat.succ n1 = Nat.succ n2 :=
  fun h =>
    match n2, h with
    | _, .refl _ => .refl _

-- We can use the `rewrite` tactic to prove this with forward reasoning.

example : ∀ n1 n2, n1 = n2 → Nat.succ n1 = Nat.succ n2 := by
  intro _ _ h
  rw [h]

-- We can use `congr` to prove this with backward reasoning.

example : ∀ n1 n2, n1 = n2 → Nat.succ n1 = Nat.succ n2 := by
  intro _ _ h
  congr

/-=============================-/
/- Injectivity of constructors -/
/-=============================-/

/-
  Given an equality between two applications of a constructor, we can conclude
  the arguments are pairwise equal.
-/

theorem successor_injective n1 n2 : Nat.succ n1 = Nat.succ n2 → n1 = n2 :=
  fun h =>
    match h with
    | .refl _ => .refl _

-- We can use the `injection` tactic to prove this.

example : ∀ n1 n2, Nat.succ n1 = Nat.succ n2 → n1 = n2 := by
  intro _ _ h
  injection h -- Generate a proof of `n1 = n2` and solve the goal.

/-==============================-/
/- Disjointness of constructors -/
/-==============================-/

/-
  Here we show how to refute the equality between applications of two different
  constructors. This only works for constructors of types in the `Type`
  universes, not `Prop`. See Lesson 5 for details about universes.
-/

theorem true_neq_false : true ≠ false := -- Unfolds to `¬(true = false)`
  fun h =>
    match (motive := ∀ z, true = z → if z then True else False) false, h with
    | _, .refl _ => True.intro

-- Fortunately, the `contradiction` tactic automates this.

example : true ≠ false := by
  intro _
  contradiction -- Prove the goal via an impossible structural equality.

/-===========-/
/- Induction -/
/-===========-/

-- Let's prove that zero is a right identity for addition.

theorem n_plus_zero_equals_n n : n + 0 = n := Eq.refl n

example : ∀ n, n + 0 = n := by
  intro n
  rfl

/-
  That was easy! Now let's try to prove that zero is also a left identity.

  ```
  theorem zero_plus_n_equals_n n : 0 + n = n := Eq.refl n
  ```

  ```
  Type mismatch
    Eq.refl n
  has type
    n = n
  but is expected to have type
    0 + n = n
  ```

  ```
  example : ∀ n, 0 + n = n := by
    intro n
    rfl
  ```

  ```
  Tactic `rfl` failed: The left-hand side
    0 + n
  is not definitionally equal to the right-hand side
    n
  ```
-/

-- What went wrong? Recall the definition of addition.

def add (n m : Nat) :=
  match m with
  | .zero => n
  | .succ p => .succ (add n p)

/-
  From this, it's clear why `n + 0 = n`. But how do we prove `0 + n = n`? We
  need *induction*. Just as we defined recursive functions in Lesson 1, we can
  use recursion to write a proof by induction.
-/

theorem zero_plus_n_equals_n n : 0 + n = n :=
  match n with
  | .zero => Eq.refl _
  | .succ p =>
    match
      (motive := ∀x, 0 + p = x → 0 + Nat.succ p = Nat.succ x)
      p, zero_plus_n_equals_n p
    with
    | _, .refl _ => .refl _

/-
  To help with doing induction in proof mode, Lean automatically constructs an
  induction principle for every inductive type. For example, here's the
  induction principle for `Nat`:
-/

#check Nat.rec

/-
  ```
  Nat.rec.{u}
    {motive : Nat → Sort u}
    (zero : motive Nat.zero)
    (succ : (n : Nat) → motive n → motive n.succ)
    (t : Nat)
  : motive t
  ```

  Let's use that induction principle to prove our theorem.
-/

example : ∀ n, 0 + n = n := by
  intro n

  /-
    We could write `apply Nat.rec`, but it's easier to just write
    `induction n`.
  -/
  induction n with

  -- Two subgoals are generated:
  | zero => rfl
  | succ _ h =>
    rw (occs := .pos [2]) [← h] -- Only rewrite the second occurrence.
    rfl

/-
  To illustrate a few more useful techniques, let's prove addition is
  commutative.
-/

theorem commutativity (n1 n2 : Nat) : n1 + n2 = n2 + n1 := by
  induction n2 with
  | zero =>
    rw [zero_plus_n_equals_n] -- We can use our previous theorem!
    rfl
  | succ p1 h1 =>
    change (n1 + p1) + 1 = p1 + 1 + n1 -- A definitionally equivalent goal
    rw [h1]
    clear h1 -- We won't need this hypothesis anymore, so remove it.
    induction n1 with -- An induction proof within an induction proof!
    | zero => rfl
    | succ p2 h2 =>
      change p1 + p2 + 1 + 1 = p1 + 1 + (p2 + 1)
      rw [h2]
      rfl

/-===================================-/
/- Automation with the `simp` tactic -/
/-===================================-/

-- The `simp` tactic rewrites the goal using known theorems, often solving it.

example : ∀ n1 n2 : Nat, n1 = n2 → 0 * n1 * 1 + n1 = n2 * 1 := by
  simp

-- We can extend the database of equations that `simp` uses. Simplification
-- happens by rewriting from left to right.

@[local simp] theorem sub_middle (n1 n2 n3 : Nat) :
  n1 + n2 + n3 - n2 = n1 + n3
:= by
  rw [Nat.add_assoc]
  rw (occs := .pos [2]) [Nat.add_comm]
  rw [← Nat.add_assoc]
  simp

-- With that lemma, the following goal can be solved automatically:

example : ∀ n1 n2 n3 : Nat, n1 + n2 + n3 - n2 - n3 = n1 := by
  simp

/-====================================-/
/- Automation with the `grind` tactic -/
/-====================================-/

-- The `grind` tactic can solve many goals by looking for contradictions.

example :
  ∀ (f : Nat → Nat) (n1 n2 n3 : Nat), f n1 = n2 → f n2 = n3 → f (f n1) = n3 :=
by
  grind

example : ∀ n1 n2 n3 : Nat, n1 * (n2 + n3) = n1 * n2 + n1 * n3 := by
  grind

-- We can also extend the database of facts that `grind` uses. See
--   https://lean-lang.org/doc/reference/latest/The--grind--tactic
--   /Annotating-Libraries-for--grind/#grind-annotation
-- for details.

/-===========-/
/- Exercises -/
/-===========-/

/-
  1. Prove `0 ≠ 1`.
  2. Prove that addition is associative, i.e.,
     `∀ n1 n2 n3 : Nat, n1 + (n2 + n3) = (n1 + n2) + n3`.
  3. Look up the induction principle for `Eq` with `#check Eq.rec`. Informally,
     what does it mean?
  4. Prove the *strong induction* principle for natural numbers:

     ```
     ∀ P : Nat → Prop,
     (∀ n1, (∀ n2, n2 < n1 → P n2) → P n1) →
     ∀ n, P n
     ```

     Hint: Start the proof with `intros`, then use a tactic called `have` to
     prove a fact involving `P` and `n`. The goal should easily follow from
     that fact.
-/

structure Name where
  name : String
deriving BEq

inductive Program where
| done : Program
| parallel : Program → Program → Program
| replicate : Program → Program
| restrict : Name → Program → Program
| send : Name → Name → Program → Program
| receive : Name → Name → Program → Program

def free (x : Name) (p : Program) : Bool :=
  match p with
  | .done => false
  | .parallel p q => free x p || free x q
  | .replicate p => free x p
  | .restrict n p => if x == n then false else free x p
  | .send n m p => if n == x || m == x then true else free x p
  | .receive n m p =>
    if n == x
    then true
    else
      if m == x
      then false
      else free x p

-- TODO: capture avoidance
def subst (x y : Name) (p : Program) : Program :=
  match p with
  | .done => p
  | .parallel p q => .parallel (subst x y p) (subst x y q)
  | .replicate p => .replicate (subst x y p)
  | .restrict n p => if x == n then p else .restrict n (subst x y p)
  | .send n m p =>
    .send (if n == x then y else n) (if m == x then y else m) (subst x y p)
  | .receive n m p =>
    .receive (if n == x then y else n) m (if m == x then p else subst x y p)

inductive Congruent : Program → Program → Prop where
| parallel_done :
  ∀ p, Congruent (.parallel p .done) p
| parallel_commute :
  ∀ p q, Congruent (.parallel p q) (.parallel q p)
| associate :
  ∀ p q r,
  Congruent (.parallel p (.parallel q r)) (.parallel (.parallel q p) r)
| restrict_done :
  ∀ n, Congruent (.restrict n .done) .done
| restrict_commute :
  ∀ n m p,
  Congruent (.restrict n (.restrict m p)) (.restrict m (.restrict n p))
| restrict_parallel :
  ∀ n p q,
  free n p = false →
  Congruent (.restrict n (.parallel p q)) (.parallel p (.restrict n q))
| replicate :
  ∀ p, Congruent (.replicate p) (.parallel p (.replicate p))
| replicate_done :
  Congruent (.replicate .done) .done
| replicate_replicate :
  ∀ p, Congruent (.replicate (.replicate p)) (.replicate p)
| replicate_parallel :
  ∀ p q,
  Congruent
    (.replicate (.parallel p q))
    (.parallel (.replicate p) (.replicate q))

theorem congruent_symmetric : ∀ p q, Congruent p q → Congruent q p := by
  intro p q h
  induction h
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry
  . sorry

inductive Reduces : Program → Program → Prop where
| cancel :
  ∀ n a b p q,
  Reduces
    (.parallel (.send n a p) (.receive n b q))
    (.parallel p (subst b a q))
| restrict :
  ∀ n p q, Reduces p q → Reduces (.restrict n p) (.restrict n q)
| parallel :
  ∀ p q r, Reduces p q → Reduces (.parallel p r) (.parallel q r)
| congruence :
  ∀ p q r s, Reduces p q → Congruent p r → Congruent q s → Reduces r s

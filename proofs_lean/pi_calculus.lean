/-
  The π-calculus is a model of concurrent computation.

  Naming conventions:
  - `p`, `q`, `s`, `t` are programs.
  - `c`, `d` are channel names for `send` and `receive`.
  - `x`, `y`, `z` are arbitrary names.
-/

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
  | .restrict y p => if x == y then false else free x p
  | .send c y p => c == x || y == x || free x p
  | .receive c y p => c == x || (y != x && free x p)

def subst_name (old new x : Name) := if x == old then new else x

inductive Subst (x y : Name) : Program → Program → Prop where
| done :
  Subst x y .done .done
| parallel :
  forall p q s t,
  Subst x y p s →
  Subst x y q t →
  Subst x y (.parallel p q) (.parallel s t)
| replicate :
  forall p q, Subst x y p q → Subst x y (.replicate p) (.replicate q)
| restrict1 :
  forall p, Subst x y (.restrict x p) (.restrict x p)
| restrict2 :
  forall z p q,
  x ≠ z →
  y ≠ z →
  Subst x y p q →
  Subst x y (.restrict z p) (.restrict z q)
| send :
  forall c z p q,
  Subst x y p q →
  Subst x y
    (.send c z p)
    (.send (subst_name x y c) (subst_name x y z) q)
| receive1 :
  forall c p,
  Subst x y (.receive c x p) (.receive (subst_name x y c) x p)
| receive2 :
  forall c z p q,
  x ≠ z →
  y ≠ z →
  Subst x y p q →
  Subst x y (.receive c z p) (.receive (subst_name x y c) z q)

inductive AlphaEquivalent : Program → Program → Prop where
| done :
  AlphaEquivalent .done .done
| parallel :
  forall p q s t,
  AlphaEquivalent p s →
  AlphaEquivalent q t →
  AlphaEquivalent (.parallel p q) (.parallel s t)
| replicate :
  forall p q,
  AlphaEquivalent p q →
  AlphaEquivalent (.replicate p) (.replicate q)
| restrict :
  forall x y z p q s t,
  free z p = false →
  free z q = false →
  Subst x z p s →
  Subst y z q t →
  AlphaEquivalent s t →
  AlphaEquivalent (.restrict x p) (.restrict y q)
| send :
  forall c x p q,
  AlphaEquivalent p q →
  AlphaEquivalent (.send c x p) (.send c x q)
| receive :
  forall c x y z p q s t,
  free z p = false →
  free z q = false →
  Subst x z p s →
  Subst y z q t →
  AlphaEquivalent s t →
  AlphaEquivalent (.receive c x p) (.receive c y q)

inductive StructurallyEquivalent : Program → Program → Prop where
| parallel_done :
  ∀ p, StructurallyEquivalent (.parallel p .done) p
| parallel_commute :
  ∀ p q, StructurallyEquivalent (.parallel p q) (.parallel q p)
| associate :
  ∀ p q s,
  StructurallyEquivalent
    (.parallel p (.parallel q s))
    (.parallel (.parallel q p) s)
| restrict_done :
  ∀ x, StructurallyEquivalent (.restrict x .done) .done
| restrict_commute :
  ∀ x y p,
  StructurallyEquivalent
    (.restrict x (.restrict y p))
    (.restrict y (.restrict x p))
| restrict_parallel :
  ∀ x p q,
  free x p = false →
  StructurallyEquivalent
    (.restrict x (.parallel p q))
    (.parallel p (.restrict x q))
| replicate :
  ∀ p, StructurallyEquivalent (.replicate p) (.parallel p (.replicate p))
| replicate_done :
  StructurallyEquivalent (.replicate .done) .done
| replicate_replicate :
  ∀ p, StructurallyEquivalent (.replicate (.replicate p)) (.replicate p)
| replicate_parallel :
  ∀ p q,
  StructurallyEquivalent
    (.replicate (.parallel p q))
    (.parallel (.replicate p) (.replicate q))

inductive Reduces : Program → Program → Prop where
| cancel :
  ∀ c x y p q s,
  Subst y x q s →
  Reduces (.parallel (.send c x p) (.receive c y q)) (.parallel p s)
| restrict :
  ∀ x p q, Reduces p q → Reduces (.restrict x p) (.restrict x q)
| parallel :
  ∀ p q s, Reduces p s → Reduces (.parallel p q) (.parallel s q)
| alpha_congruent :
  ∀ p q r s,
  Reduces p q →
  AlphaEquivalent p r →
  AlphaEquivalent q s →
  Reduces r s
| structurally_congruent :
  ∀ p q r s,
  Reduces p q →
  StructurallyEquivalent p r →
  StructurallyEquivalent q s →
  Reduces r s

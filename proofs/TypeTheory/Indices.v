(**************************************************************************)
(**************************************************************************)
(****                                                                  ****)
(****   A demonstration that instead of having inductive families      ****)
(****   (i.e., inductive types with indices) built into the type       ****)
(****   theory, we can emulate them with families of inductive types   ****)
(****   (i.e., inductive types with parameters) if propositional       ****)
(****   equality is taken to be primitive.                             ****)
(****                                                                  ****)
(**************************************************************************)
(**************************************************************************)

Inductive Exp1 : Set -> Type :=
| Zero : Exp1 nat
| Succ : Exp1 nat -> Exp1 nat
| Pair : forall b c, Exp1 b -> Exp1 c -> Exp1 (prod b c).

Fixpoint eval1 (a : Set) (e1 : Exp1 a) : a :=
  match e1 in Exp1 b return b with
  | Zero => 0
  | Succ e2 => eval1 nat e2 + 1
  | Pair c d e2 e3 => (eval1 c e2, eval1 d e3)
  end.

Inductive Exp2 (a : Set) : Type :=
| Zero2 : nat = a -> Exp2 a
| Succ2 : nat = a -> Exp2 a -> Exp2 a
| Pair2 : forall (b c : Set), (prod b c) = a -> Exp2 b -> Exp2 c -> Exp2 a.

Fixpoint eval2 (a : Set) (e1 : Exp2 a) : a :=
  match e1 with
  | Zero2 _ H => match H in (_ = b) return b with
                 | eq_refl => 0
                 end
  | Succ2 _ H e2 => match H in (_ = b) return b with
                    | eq_refl => eval2 nat (
                                   match (eq_sym H)
                                   in (_ = c)
                                   return Exp2 c with
                                   | eq_refl => e2
                                   end
                                 ) + 1
                    end
  | Pair2 _ b c H e2 e3 => match H in (_ = b) return b with
                           | eq_refl => (eval2 b e2, eval2 c e3)
                           end
  end.

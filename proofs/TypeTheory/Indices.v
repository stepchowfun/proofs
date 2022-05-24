(**************************************************************************)
(**************************************************************************)
(****                                                                  ****)
(****   A demonstration that instead of having inductive families      ****)
(****   (i.e., inductive types with indices) built into the type       ****)
(****   theory, we can emulate them with families of inductive types   ****)
(****   (i.e., inductive types with parameters) if propositional       ****)
(****   equality is taken to be primitive                              ****)
(****                                                                  ****)
(**************************************************************************)
(**************************************************************************)

Require Import Main.Tactics.

Inductive exp1 : Set -> Type :=
| zero1 : exp1 nat
| succ1 : exp1 nat -> exp1 nat
| pair1 : forall b c, exp1 b -> exp1 c -> exp1 (prod b c).

Fixpoint eval1 (a : Set) (e1 : exp1 a) : a :=
  match e1 in exp1 b return b with
  | zero1 => 0
  | succ1 e2 => eval1 nat e2 + 1
  | pair1 c d e2 e3 => (eval1 c e2, eval1 d e3)
  end.

Inductive exp2 (a : Set) : Type :=
| zero2 : nat = a -> exp2 a
| succ2 : nat = a -> exp2 a -> exp2 a
| pair2 : forall (b c : Set), (prod b c) = a -> exp2 b -> exp2 c -> exp2 a.

Fixpoint eval2 (a : Set) (e1 : exp2 a) : a :=
  match e1 with
  | zero2 _ H =>
    match H in (_ = b) return b with
    | eq_refl => 0
    end
  | succ2 _ H e2 =>
    match H in (_ = b) return b with
    | eq_refl =>
      eval2 nat (
        match (eq_sym H) in (_ = c) return exp2 c with
        | eq_refl => e2
        end
      ) + 1
    end
  | pair2 _ b c H e2 e3 =>
    match H in (_ = b) return b with
    | eq_refl => (eval2 b e2, eval2 c e3)
    end
  end.

Fixpoint exp1ToExp2 (a : Set) (e1 : exp1 a) : exp2 a :=
  match e1 with
  | zero1 => zero2 nat eq_refl
  | succ1 e2 => succ2 nat eq_refl (exp1ToExp2 nat e2)
  | pair1 c d e2 e3 =>
    pair2 (prod c d) c d eq_refl (exp1ToExp2 c e2) (exp1ToExp2 d e3)
  end.

Fixpoint exp2ToExp1 (a : Set) (e1 : exp2 a) : exp1 a :=
  match e1 with
  | zero2 _ H =>
    match H in (_ = b) return exp1 b with
    | eq_refl => zero1
    end
  | succ2 _ H e2 =>
    match H in (_ = b) return exp1 b with
    | eq_refl =>
      succ1 (
        exp2ToExp1
          nat
          match (eq_sym H) in (_ = b) return exp2 b with
          | eq_refl => e2
          end
      )
    end
  | pair2 _ c d H e2 e3 =>
    match H in (_ = b) return exp1 b with
    | eq_refl =>
      pair1 c d (exp2ToExp1 c e2) (exp2ToExp1 d e3)
    end
  end.

Theorem exp1ToExp2Homomorphism :
  forall (a : Set) (e : exp1 a), eval1 a e = eval2 a (exp1ToExp2 a e).
Proof.
  clean.
  induction e; magic.
Qed.

#[export] Hint Resolve exp1ToExp2Homomorphism : main.

Theorem exp2ToExp1Homomorphism :
  forall (a : Set) (e : exp2 a), eval2 a e = eval1 a (exp2ToExp1 a e).
Proof.
  clean.
  induction e; magic.
Qed.

#[export] Hint Resolve exp2ToExp1Homomorphism : main.

Theorem exp1ToExp2Isomorphism :
  forall (a : Set) (e : exp1 a), exp2ToExp1 a (exp1ToExp2 a e) = e.
Proof.
  clean.
  induction e; magic.
Qed.

#[export] Hint Resolve exp1ToExp2Isomorphism : main.

Theorem exp2ToExp1Isomorphism :
  forall (a : Set) (e : exp2 a), exp1ToExp2 a (exp2ToExp1 a e) = e.
Proof.
  clean.
  induction e; magic.
Qed.

#[export] Hint Resolve exp2ToExp1Isomorphism : main.

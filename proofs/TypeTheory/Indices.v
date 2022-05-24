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

Require Import Coq.Init.Nat.
Require Import Main.Tactics.

Inductive exp1 : Set -> Type :=
| const1 : forall (a : Set), a -> exp1 a
| add1 : exp1 nat -> exp1 nat -> exp1 nat
| lessThan1 : exp1 nat -> exp1 nat -> exp1 bool.

#[export] Hint Constructors exp1 : main.

Inductive exp2 (a : Set) : Type :=
| const2 : a -> exp2 a
| add2 : nat = a -> exp2 nat -> exp2 nat -> exp2 a
| lessThan2 : bool = a -> exp2 nat -> exp2 nat -> exp2 a.

#[export] Hint Constructors exp2 : main.

Fixpoint eval1 (a : Set) (e1 : exp1 a) : a :=
  match e1 in exp1 b return b with
  | const1 _ x => x
  | add1 e2 e3 => eval1 nat e2 + eval1 nat e3
  | lessThan1 e2 e3 => ltb (eval1 nat e2) (eval1 nat e3)
  end.

Fixpoint eval2 (a : Set) (e1 : exp2 a) : a :=
  match e1 with
  | const2 _ x => x
  | add2 _ H e2 e3 =>
    match H in (_ = b) return b with
    | eq_refl => eval2 nat e2 + eval2 nat e3
    end
  | lessThan2 _ H e2 e3 =>
    match H in (_ = b) return b with
    | eq_refl => ltb (eval2 nat e2) (eval2 nat e3)
    end
  end.

Fixpoint exp1ToExp2 (a : Set) (e1 : exp1 a) : exp2 a :=
  match e1 with
  | const1 b x => const2 b x
  | add1 e2 e3 => add2 nat eq_refl (exp1ToExp2 nat e2) (exp1ToExp2 nat e3)
  | lessThan1 e2 e3 =>
    lessThan2 bool eq_refl (exp1ToExp2 nat e2) (exp1ToExp2 nat e3)
  end.

Fixpoint exp2ToExp1 (a : Set) (e1 : exp2 a) : exp1 a :=
  match e1 with
  | const2 _ x => const1 a x
  | add2 _ H e2 e3 =>
    match H in (_ = b) return exp1 b with
    | eq_refl => add1 (exp2ToExp1 nat e2) (exp2ToExp1 nat e3)
    end
  | lessThan2 _ H e2 e3 =>
    match H in (_ = b) return exp1 b with
    | eq_refl => lessThan1 (exp2ToExp1 nat e2) (exp2ToExp1 nat e3)
    end
  end.

Theorem exp1ToExp2Homomorphism :
  forall (a : Set) (e : exp1 a), eval1 a e = eval2 a (exp1ToExp2 a e).
Proof.
  clean.
  induction e; magic.
  clean.
  rewrite IHe1.
  rewrite IHe2.
  magic.
Qed.

#[export] Hint Resolve exp1ToExp2Homomorphism : main.

Theorem exp2ToExp1Homomorphism :
  forall (a : Set) (e : exp2 a), eval2 a e = eval1 a (exp2ToExp1 a e).
Proof.
  clean.
  induction e; magic.
  clean.
  rewrite IHe1.
  rewrite IHe2.
  magic.
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

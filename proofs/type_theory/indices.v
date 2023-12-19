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
Require Import main.tactics.

(*
  We define two inductive definitions and prove they are isomorphic. The first
  definition is an inductive family, and the second is a family of inductive
  types.

  Note that `exp1` lives in `Type` because its `const1` constructor quantifies
  over `Set`. `exp2`, however, can live in `Set` since parameter arguments are
  not considered for universe constraints on inductive data types. In that
  sense, we have gained something from using a parameter instead of an index.
*)

Inductive Exp1 : Set -> Type :=
| const1 : forall (a : Set), a -> Exp1 a
| add1 : Exp1 nat -> Exp1 nat -> Exp1 nat
| less_than1 : Exp1 nat -> Exp1 nat -> Exp1 bool.

#[export] Hint Constructors Exp1 : main.

Inductive Exp2 (a : Set) : Set :=
| const2 : a -> Exp2 a
| add2 : nat = a -> Exp2 nat -> Exp2 nat -> Exp2 a
| less_than2 : bool = a -> Exp2 nat -> Exp2 nat -> Exp2 a.

#[export] Hint Constructors Exp2 : main.

Fixpoint exp1_to_exp2 (a : Set) (e1 : Exp1 a) : Exp2 a :=
  match e1 with
  | const1 b x => const2 b x
  | add1 e2 e3 => add2 nat eq_refl (exp1_to_exp2 nat e2) (exp1_to_exp2 nat e3)
  | less_than1 e2 e3 =>
    less_than2 bool eq_refl (exp1_to_exp2 nat e2) (exp1_to_exp2 nat e3)
  end.

Fixpoint exp2_to_exp1 (a : Set) (e1 : Exp2 a) : Exp1 a :=
  match e1 with
  | const2 _ x => const1 a x
  | add2 _ H e2 e3 =>
    match H in (_ = b) return Exp1 b with
    | eq_refl => add1 (exp2_to_exp1 nat e2) (exp2_to_exp1 nat e3)
    end
  | less_than2 _ H e2 e3 =>
    match H in (_ = b) return Exp1 b with
    | eq_refl => less_than1 (exp2_to_exp1 nat e2) (exp2_to_exp1 nat e3)
    end
  end.

Theorem exp1_to_exp2_to_exp1 :
  forall (a : Set) (e : Exp1 a), exp2_to_exp1 a (exp1_to_exp2 a e) = e.
Proof.
  clean.
  induction e; search.
Qed.

#[export] Hint Resolve exp1_to_exp2_to_exp1 : main.

Theorem exp2_to_exp1_to_exp2 :
  forall (a : Set) (e : Exp2 a), exp1_to_exp2 a (exp2_to_exp1 a e) = e.
Proof.
  clean.
  induction e; search.
Qed.

#[export] Hint Resolve exp2_to_exp1_to_exp2 : main.

(*
  Just for fun, we implement evaluators for both of the inductive definitions
  and prove they are preserved by the isomorphisms.
*)

Fixpoint eval1 (a : Set) (e1 : Exp1 a) : a :=
  match e1 in Exp1 b return b with
  | const1 _ x => x
  | add1 e2 e3 => eval1 nat e2 + eval1 nat e3
  | less_than1 e2 e3 => ltb (eval1 nat e2) (eval1 nat e3)
  end.

Fixpoint eval2 (a : Set) (e1 : Exp2 a) : a :=
  match e1 with
  | const2 _ x => x
  | add2 _ H e2 e3 =>
    match H in (_ = b) return b with
    | eq_refl => eval2 nat e2 + eval2 nat e3
    end
  | less_than2 _ H e2 e3 =>
    match H in (_ = b) return b with
    | eq_refl => ltb (eval2 nat e2) (eval2 nat e3)
    end
  end.

Theorem exp1_to_exp2_preserves_eval :
  forall (a : Set) (e : Exp1 a), eval1 a e = eval2 a (exp1_to_exp2 a e).
Proof.
  clean.
  induction e; search.
  clean.
  rewrite IHe1.
  rewrite IHe2.
  search.
Qed.

#[export] Hint Resolve exp1_to_exp2_preserves_eval : main.

Theorem exp2_to_exp1_preserves_eval :
  forall (a : Set) (e : Exp2 a), eval2 a e = eval1 a (exp2_to_exp1 a e).
Proof.
  clean.
  induction e; search.
  clean.
  rewrite IHe1.
  rewrite IHe2.
  search.
Qed.

#[export] Hint Resolve exp2_to_exp1_preserves_eval : main.

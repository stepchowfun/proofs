(*************************************************************)
(*************************************************************)
(****                                                     ****)
(****   A basic introduction to theorem proving in Coq.   ****)
(****                                                     ****)
(*************************************************************)
(*************************************************************)

(***********************************)
(* Ordinary functional programming *)
(***********************************)

(* In Haskell, we would write: data Bool = True | False *)

Inductive bool : Set :=
| true : bool
| false : bool.

Definition negb b :=
  match b with
  | true => false
  | false => true
  end.

Compute negb true.
Compute negb false.

Definition andb b1 b2 :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb b1 b2 :=
  match b1 with
  | true => true
  | false => b2
  end.

(* In Haskell, we would write: data Nat = Zero | Succ n *)

Inductive nat : Set :=
| zero : nat
| succ : nat -> nat.

Check zero.
Check succ zero.
Check succ (succ zero).

Fixpoint plus n m :=
  match n with
    | zero => m
    | succ p => succ (plus p m)
  end.

Compute plus (succ zero) (succ zero).

(*******************)
(* Predicate logic *)
(*******************)

Inductive True : Prop :=
| trivial : True.

Inductive False : Prop := .

Inductive and P Q : Prop :=
| conj : P -> Q -> (and P Q).

Definition iff P Q := and (P -> Q) (Q -> P).

Inductive or P Q : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.

Definition not A := A -> False.

Inductive eq (X : Set) : X -> X -> Prop :=
| refl_equal : forall x, eq X x x.

(*********************)
(* Let's do a proof! *)
(*********************)

(* Let's prove that two is even. First, we have to define what "even" means. *)

Inductive even : nat -> Prop :=
| even_zero : even zero
| even_succ : forall n, odd n -> even (succ n)

(* We also have to define what "odd" means. *)

with odd : nat -> Prop :=
  odd_succ : forall n, even n -> odd (succ n).

(* We can manually write out the proof term as follows: *)

Definition two_even_a : even (succ (succ zero)) :=
  even_succ (succ zero) (odd_succ zero even_zero).

(* Alternatively, we can prove it using tactics: *)

Theorem two_even_b : even (succ (succ zero)).
Proof.
  apply even_succ.
  apply odd_succ.
  apply even_zero.
Qed.

(* Let's prove that addition is associative. *)

Theorem plus_assoc : forall n m p : nat,
  plus n (plus m p) = plus (plus n m) p.
Proof.
  intros n m p.
  induction n.
  - reflexivity.
  - simpl.
    rewrite -> IHn.
    reflexivity.
Qed.

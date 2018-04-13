(************************************************************)
(************************************************************)
(****                                                    ****)
(****   A basic introduction to theorem proving in Coq   ****)
(****                                                    ****)
(************************************************************)
(************************************************************)

(***********************************)
(* Ordinary functional programming *)
(***********************************)

(* In Haskell, we would write `data Bool = True | False`. *)

Inductive bool :=
| true : bool
| false : bool.

Definition negb b :=
  match b with
  | true => false
  | false => true
  end.

(*
  Let's compute some examples. In general, it's bad practice to have vernacular
  commands like these in the proof script. But it's fine for teaching.
*)

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

(* In Haskell, we would write `data Nat = Zero | Succ n`. *)

Inductive nat :=
| zero : nat
| succ : nat -> nat.

(* The `Check` command tells us the type of a given term. *)

Check zero.
Check succ zero.
Check succ (succ zero).

Fixpoint plus n m :=
  match n with
  | zero => m
  | succ p => succ (plus p m)
  end.

(* Let's show that 1 + 1 = 2. *)

Compute plus (succ zero) (succ zero).

(*******************)
(* Predicate logic *)
(*******************)

Inductive True : Prop :=
| trivial : True.

Inductive False : Prop := .

Inductive and P Q : Prop :=
| conj : P -> Q -> and P Q.

Definition iff P Q := and (P -> Q) (Q -> P).

Inductive or P Q : Prop :=
| orIntroL : P -> or P Q
| orIntroR : Q -> or P Q.

Definition not A := A -> False.

(*************************)
(* Let's do some proofs! *)
(*************************)

(* Let's prove that two is even. First, we have to define what "even" means. *)

Inductive even : nat -> Prop :=
| evenZero : even zero
| evenSS : forall n, even n -> even (succ (succ n)).

(* We can manually write out the proof term as follows: *)

Definition twoEvenA : even (succ (succ zero)) := evenSS zero evenZero.

(*
  Alternatively, we can prove it using tactics in proof mode. This is generally
  easier than writing proof terms by hand.
*)

Theorem twoEvenB : even (succ (succ zero)).
Proof.
  apply evenSS.
  apply evenZero.
Qed.

(* Let's prove that a number is either even or odd. *)

Inductive odd : nat -> Prop :=
| oddOne : odd (succ zero)
| oddSS : forall n, odd n -> odd (succ (succ n)).

(*
  First, we need to prove this lemma so we can do induction on n and n + 1 at
  the same time.
*)

Theorem doubleInd :
  forall P : nat -> Prop,
  P zero ->
  P (succ zero) ->
  (forall n, P n /\ P (succ n) -> P (succ (succ n))) ->
  forall n,
  P n /\ P (succ n).
Proof.
  intros.
  induction n.
  - split; assumption.
  - destruct IHn.
    split.
    + assumption.
    + apply H1.
      split; assumption.
Qed.

(* Now we can prove the main result: forall n, even n \/ odd n. *)

Theorem evenOrOdd : forall n, even n \/ odd n.
Proof.
  apply doubleInd.
  - left.
    apply evenZero.
  - right.
    apply oddOne.
  - intros.
    destruct H.
    destruct H;
      destruct H0;
      left + right;
      apply evenSS + apply oddSS;
      assumption.
Qed.

(* Let's prove that addition is associative. *)

Theorem plusAssoc : forall n m p : nat,
  plus n (plus m p) = plus (plus n m) p.
Proof.
  intros.
  induction n.
  - reflexivity.
  - cbn.
    rewrite IHn.
    reflexivity.
Qed.

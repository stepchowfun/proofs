(*********************************)
(*********************************)
(****                         ****)
(****   Proof by reflection   ****)
(****                         ****)
(*********************************)
(*********************************)

(**********************)
(* General reflection *)
(**********************)

Inductive reflect (P : Prop) : bool -> Prop :=
| reflectT : P -> reflect P true
| reflectF : ~ P -> reflect P false.

Theorem reflectIff : forall P b, (P <-> b = true) <-> reflect P b.
Proof.
  split.
  - destruct b; constructor.
    + destruct H. auto.
    + intro. destruct H. discriminate (H H0).
  - split; intro; destruct H; auto.
    + destruct H. auto.
    + discriminate H0.
Qed.

#[export] Hint Resolve -> reflectIff : main.
#[export] Hint Resolve <- reflectIff : main.

Ltac reflect H1 :=
  let H2 := fresh "H" in
  let H3 := fresh "H" in
  solve [pose (H2 := H1); inversion H2 as [ H3 | H3 ]; exact H3].

(*********************)
(* Example: evenness *)
(*********************)

(*
  Two definitions of evenness:
  1. an inductive proposition
  2. a decision procedure
*)

Inductive even : nat -> Prop :=
| evenZero : even 0
| evenSS : forall n : nat, even n -> even (S (S n)).

#[export] Hint Constructors even : main.

Fixpoint isEven n :=
  match n with
  | O => true
  | S O => false
  | S (S x) => isEven x
  end.

(* A proof that `even n` is reflected in `isEven n` *)

Theorem evenInd :
  forall P : nat -> Prop,
  P 0 ->
  P 1 ->
  (forall n, P n /\ P (S n) -> P (S (S n))) ->
  forall n,
  P n /\ P (S n).
Proof.
  induction n; auto.
  split; auto.
  apply IHn.
Qed.

#[export] Hint Resolve evenInd : main.

Theorem evenIffIsEven : forall n, even n <-> isEven n = true.
Proof.
  split.
  - intro. induction H; auto.
  - generalize dependent n.
    pose (P := fun n => isEven n = true -> even n).
    assert (forall n, P n /\ P (S n)).
    + apply evenInd; unfold P.
      * constructor.
      * intro. inversion H.
      * intros. constructor. assert (isEven n = true); auto. destruct H. auto.
    + intros. destruct (H n). unfold P in H1. auto.
Qed.

#[export] Hint Resolve -> evenIffIsEven : main.
#[export] Hint Resolve <- evenIffIsEven : main.

Theorem evenRefl : forall n, reflect (even n) (isEven n).
Proof.
  intro.
  apply reflectIff.
  split; auto with main.
Qed.

(* A proof by reflection of `even 1000` *)

Theorem evenOneThousand : even 1000.
Proof.
  reflect (evenRefl 1000).
Qed.

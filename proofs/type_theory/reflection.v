(*********************************)
(*********************************)
(****                         ****)
(****   Proof by reflection   ****)
(****                         ****)
(*********************************)
(*********************************)

(*************************************)
(* General reflection infrastructure *)
(*************************************)

Inductive Reflect (P : Prop) : bool -> Prop :=
| reflect_true : P -> Reflect P true
| reflect_false : ~ P -> Reflect P false.

Theorem reflect_iff : forall P b, (P <-> b = true) <-> Reflect P b.
Proof.
  split.
  - destruct b; constructor.
    + destruct H. auto.
    + intro. destruct H. discriminate (H H0).
  - split; intro; destruct H; auto.
    + destruct H. auto.
    + discriminate H0.
Qed.

#[export] Hint Resolve -> reflect_iff : main.
#[export] Hint Resolve <- reflect_iff : main.

Ltac reflect b :=
  let H1 := fresh "H" in
  let H2 := fresh "H" in
  let H3 := fresh "H" in
  solve [
    evar (H1 : Prop);
    assert (H2 : Reflect H1 b); subst H1; [
      auto with main |
      inversion H2 as [H3 | H3]; exact H3
    ]
  ].

(*********************)
(* Example: evenness *)
(*********************)

(*
  Two definitions of evenness:
  1. an inductive predicate
  2. a decision procedure
*)

Inductive Even : nat -> Prop :=
| even_zero : Even 0
| even_ss : forall n : nat, Even n -> Even (S (S n)).

#[export] Hint Constructors Even : main.

Fixpoint is_even n :=
  match n with
  | O => true
  | S O => false
  | S (S x) => is_even x
  end.

(* A proof that `Even n` is reflected in `is_even n` *)

Theorem even_ind :
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

Theorem even_refl : forall n, Reflect (Even n) (is_even n).
Proof.
  intro.
  apply reflect_iff.
  split.
  - intro. induction H; auto.
  - generalize dependent n.
    pose (P := fun n => is_even n = true -> Even n).
    assert (forall n, P n /\ P (S n)).
    + apply even_ind; unfold P.
      * constructor.
      * intro. inversion H.
      * intros. constructor. assert (is_even n = true); auto. destruct H. auto.
    + intros. destruct (H n). unfold P in H1. auto.
Qed.

#[export] Hint Resolve even_refl : main.

(* A proof by reflection of `Even 1000` *)

Theorem even_one_thousand : Even 1000.
Proof.
  reflect (is_even 1000).
Qed.

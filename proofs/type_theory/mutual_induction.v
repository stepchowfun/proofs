(******************************)
(******************************)
(****                      ****)
(****   Mutual induction   ****)
(****                      ****)
(******************************)
(******************************)

(* Consider these two types defined by mutual induction. *)

Inductive Even : nat -> Type :=
| zero : Even 0
| from_odd : forall n, Odd n -> Even (S n)

with Odd : nat -> Type :=
| from_even : forall n, Even n -> Odd (S n).

(* Let's try to prove that Even numbers are divisible by 2. *)

Goal forall n, Even n -> exists m, n = 2 * m.
Proof.
  intros.
  induction H.
  - eauto.
  - (* Now what? *)
Abort.

(* The default induction principles for these types are too weak. *)

Check Even_ind.

(*
  ```
  Even_ind
    : forall P : forall n : nat, Even n -> Prop,
        P 0 zero ->
        (forall (n : nat) (o : Odd n), P (S n) (from_odd n o)) ->
        forall (n : nat) (e : Even n), P n e
  ```
*)

Check Odd_ind.

(*
  ```
  Odd_ind
    : forall P : forall n : nat, Odd n -> Prop,
        (forall (n : nat) (e : Even n), P (S n) (from_even n e)) ->
        forall (n : nat) (o : Odd n), P n o
  ```
*)

(* We can ask Coq to generate stronger ones. *)

Scheme Even_mut_ind := Induction for Even Sort Prop
  with Odd_mut_ind := Induction for Odd Sort Prop.

Check Even_mut_ind.

(*
  ```
  Even_mut_ind
    : forall (P : forall n : nat, Even n -> Prop)
          (P0 : forall n : nat, Odd n -> Prop),
        P 0 zero ->
        (forall (n : nat) (o : Odd n), P0 n o -> P (S n) (from_odd n o)) ->
        (forall (n : nat) (e : Even n), P n e -> P0 (S n) (from_even n e)) ->
        forall (n : nat) (e : Even n), P n e
  ```
*)

Check Odd_mut_ind.

(*
  ```
  Odd_mut_ind
    : forall (P : forall n : nat, Even n -> Prop)
          (P0 : forall n : nat, Odd n -> Prop),
        P 0 zero ->
        (forall (n : nat) (o : Odd n), P0 n o -> P (S n) (from_odd n o)) ->
        (forall (n : nat) (e : Even n), P n e -> P0 (S n) (from_even n e)) ->
        forall (n : nat) (o : Odd n), P0 n o
  ```
*)

(* Now we can do that proof. *)

Goal forall n, Even n -> exists m, n = 2 * m.
Proof.
  apply Even_mut_ind with (P0 := fun n H => exists m : nat, S n = 2 * m).
  - eauto.
  - auto.
  - intros.
    destruct H.
    exists (S x).
    rewrite H.
    cbn.
    auto.
Qed.

(* Mutual induction can be emulated with an index. *)

Inductive ParityBit := pb_even | pb_odd.

Inductive Parity : ParityBit -> nat -> Type :=
| p_zero : Parity pb_even 0
| p_from_odd : forall n, Parity pb_odd n -> Parity pb_even (S n)
| p_from_even : forall n, Parity pb_even n -> Parity pb_odd (S n).

Check Parity_ind.

(*
  ```
  Parity_ind
    : forall P : forall (p : ParityBit) (n : nat), Parity p n -> Prop,
        P pb_even 0 p_zero ->
        (forall (n : nat) (p : Parity pb_odd n),
          P pb_odd n p -> P pb_even (S n) (p_from_odd n p)) ->
        (forall (n : nat) (p : Parity pb_even n),
          P pb_even n p -> P pb_odd (S n) (p_from_even n p)) ->
        forall (p : ParityBit) (n : nat) (p0 : Parity p n), P p n p0
  ```
*)

(* Let's do that proof one last time. *)

Goal forall n, Parity pb_even n -> exists m, n = 2 * m.
Proof.
  intro.
  assert (
    forall pb,
    Parity pb n ->
    match pb with
    | pb_even => exists m, n = 2 * m
    | pb_odd => exists m, S n = 2 * m
    end
  ).
  - intros.
    induction H.
    + eauto.
    + auto.
    + destruct IHParity.
      exists (S x).
      rewrite H0.
      cbn.
      auto.
  - intro.
    specialize (H _ H0).
    eauto.
Qed.

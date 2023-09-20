(******************************)
(******************************)
(****                      ****)
(****   Mutual induction   ****)
(****                      ****)
(******************************)
(******************************)

(* Consider these two types defined by mutual induction. *)

Inductive even : nat -> Type :=
| zero : even 0
| fromOdd : forall n, odd n -> even (S n)

with odd : nat -> Type :=
| fromEven : forall n, even n -> odd (S n).

(* Let's try to prove that even numbers are divisible by 2. *)

Goal forall n, even n -> exists m, n = 2 * m.
Proof.
  intros.
  induction H.
  - eauto.
  - (* Now what? *)
Abort.

(* The default induction principles for these types are too weak. *)

Check even_ind.

(*
  ```
  even_ind
    : forall P : forall n : nat, even n -> Prop,
        P 0 zero ->
        (forall (n : nat) (o : odd n), P (S n) (fromOdd n o)) ->
        forall (n : nat) (e : even n), P n e
  ```
*)

Check odd_ind.

(*
  ```
  odd_ind
    : forall P : forall n : nat, odd n -> Prop,
        (forall (n : nat) (e : even n), P (S n) (fromEven n e)) ->
        forall (n : nat) (o : odd n), P n o
  ```
*)

(* We can ask Coq to generate stronger ones. *)

Scheme even_mut_ind := Induction for even Sort Prop
  with odd_mut_ind := Induction for odd Sort Prop.

Check even_mut_ind.

(*
  ```
  even_mut_ind
    : forall (P : forall n : nat, even n -> Prop)
          (P0 : forall n : nat, odd n -> Prop),
        P 0 zero ->
        (forall (n : nat) (o : odd n), P0 n o -> P (S n) (fromOdd n o)) ->
        (forall (n : nat) (e : even n), P n e -> P0 (S n) (fromEven n e)) ->
        forall (n : nat) (e : even n), P n e
  ```
*)

Check odd_mut_ind.

(*
  ```
  odd_mut_ind
    : forall (P : forall n : nat, even n -> Prop)
          (P0 : forall n : nat, odd n -> Prop),
        P 0 zero ->
        (forall (n : nat) (o : odd n), P0 n o -> P (S n) (fromOdd n o)) ->
        (forall (n : nat) (e : even n), P n e -> P0 (S n) (fromEven n e)) ->
        forall (n : nat) (o : odd n), P0 n o
  ```
*)

(* Now we can do that proof. *)

Goal forall n, even n -> exists m, n = 2 * m.
Proof.
  apply even_mut_ind with (P0 := fun n H => exists m : nat, S n = 2 * m).
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

Inductive parityBit := pbEven | pbOdd.

Inductive parity : parityBit -> nat -> Type :=
| pZero : parity pbEven 0
| pFromOdd : forall n, parity pbOdd n -> parity pbEven (S n)
| pFromEven : forall n, parity pbEven n -> parity pbOdd (S n).

Check parity_ind.

(*
  ```
  parity_ind
    : forall P : forall (p : parityBit) (n : nat), parity p n -> Prop,
        P pbEven 0 pZero ->
        (forall (n : nat) (p : parity pbOdd n),
          P pbOdd n p -> P pbEven (S n) (pFromOdd n p)) ->
        (forall (n : nat) (p : parity pbEven n),
          P pbEven n p -> P pbOdd (S n) (pFromEven n p)) ->
        forall (p : parityBit) (n : nat) (p0 : parity p n), P p n p0
  ```
*)

(* Let's do that proof one last time. *)

Goal forall n, parity pbEven n -> exists m, n = 2 * m.
Proof.
  intro.
  assert (
    forall pb,
    parity pb n ->
    match pb with
    | pbEven => exists m, n = 2 * m
    | pbOdd => exists m, S n = 2 * m
    end
  ).
  - intros.
    induction H.
    + eauto.
    + auto.
    + destruct IHparity.
      exists (S x).
      rewrite H0.
      cbn.
      auto.
  - intro.
    specialize (H _ H0).
    eauto.
Qed.

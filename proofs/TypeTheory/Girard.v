(******************************)
(******************************)
(****                      ****)
(****   Girard's paradox   ****)
(****                      ****)
(******************************)
(******************************)

#[local] Unset Universe Checking.

Definition exfalso := forall (p : Type), p.
Definition negate := fun (phi : Type) => phi -> exfalso.
Definition power := fun (S : Type) => S -> Type.
Definition universe :=
  forall (X : Type),
    ((power (power X) -> X) -> power (power X)).
Definition tau :=
  fun (t : power (power universe)) =>
    fun (X : Type) =>
      fun (f : power (power X) -> X) =>
        fun (p : power X) =>
          t (fun (x : universe) => p (f (x X f))).
Definition sigma :=
  fun (s : universe) =>
    s universe (fun (t : power (power universe)) => tau t).
Definition delta :=
  fun (y : universe) =>
    negate (forall (p : power universe), sigma y p -> p (tau (sigma y))).
Definition omega :=
  tau (fun (p : power universe) => forall (x : universe), sigma x p -> p x).

Definition bad := (
  fun (
    zero :
      forall (p : power universe),
        (forall (x : universe), sigma x p -> p x) -> p omega
  ) => (
    zero delta (
      fun (x : universe) =>
        fun (two : sigma x delta) =>
          fun (
            three :
              forall (p : power universe), sigma x p -> p (tau (sigma x))
          ) => three delta two (
            fun (p : power universe) =>
              three (fun (y : universe) => p (tau (sigma y)))
          )
    )
  ) (
    fun (p : power universe) => zero (fun (y : universe) => p (tau (sigma y)))
  )
) (
  fun (p : power universe) =>
    fun (one : forall (x : universe), sigma x p -> p x) =>
      one omega (fun (x : universe) => one (tau (sigma x)))
).

Check bad. (* `exfalso` *)
Check bad False. (* `False` *)

(*
  ```
  Compute bad.
  Compute bad False.
  ```
*)

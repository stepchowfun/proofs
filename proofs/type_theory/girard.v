(******************************)
(******************************)
(****                      ****)
(****   Girard's paradox   ****)
(****                      ****)
(******************************)
(******************************)

(*
  Girard's paradox shows that any type is inhabited if `Type : Type`. The
  presentation of the paradox was adapted from this paper:

    Antonius J. C. Hurkens. 1995. A Simplification of Girard's Paradox. In
    Proceedings of the Second International Conference on Typed Lambda Calculi
    and Applications (TLCA '95). Springer-Verlag, Berlin, Heidelberg, 266-278.

  To demonstrate the paradox, we first need to disable universe checking.
*)

#[local] Unset Universe Checking.

Definition ExFalso := forall (P : Type), P.
Definition Negate := fun (Phi : Type) => Phi -> ExFalso.
Definition Power := fun (S : Type) => S -> Type.
Definition U :=
  forall (X : Type),
    ((Power (Power X) -> X) -> Power (Power X)).
Definition Tau :=
  fun (T : Power (Power U)) =>
    fun (X : Type) =>
      fun (F : Power (Power X) -> X) =>
        fun (P : Power X) =>
          T (fun (Y : U) => P (F (Y X F))).
Definition Sigma :=
  fun (s : U) =>
    s U (fun (t : Power (Power U)) => Tau t).
Definition Delta :=
  fun (y : U) =>
    Negate (forall (P : Power U), Sigma y P -> P (Tau (Sigma y))).
Definition Omega :=
  Tau (fun (P : Power U) => forall (X : U), Sigma X P -> P X).

Definition bad := (
  fun (
    Zero :
      forall (P : Power U),
        (forall (X : U), Sigma X P -> P X) -> P Omega
  ) => (
    Zero Delta (
      fun (X : U) =>
        fun (Two : Sigma X Delta) =>
          fun (
            Three :
              forall (P : Power U), Sigma X P -> P (Tau (Sigma X))
          ) => Three Delta Two (
            fun (P : Power U) =>
              Three (fun (y : U) => P (Tau (Sigma y)))
          )
    )
  ) (
    fun (P : Power U) => Zero (fun (y : U) => P (Tau (Sigma y)))
  )
) (
  fun (P : Power U) =>
    fun (One : forall (X : U), Sigma X P -> P X) =>
      One Omega (fun (X : U) => One (Tau (Sigma X)))
).

Check bad. (* `ExFalso` *)
Check bad False. (* `False` *)

(*
  ```
  Compute bad.
  Compute bad False.
  ```
*)

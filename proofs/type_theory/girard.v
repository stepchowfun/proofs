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
Definition Universe :=
  forall (X : Type),
    ((Power (Power X) -> X) -> Power (Power X)).
Definition Tau :=
  fun (T : Power (Power Universe)) =>
    fun (X : Type) =>
      fun (F : Power (Power X) -> X) =>
        fun (P : Power X) =>
          T (fun (Y : Universe) => P (F (Y X F))).
Definition Sigma :=
  fun (s : Universe) =>
    s Universe (fun (t : Power (Power Universe)) => Tau t).
Definition Delta :=
  fun (y : Universe) =>
    Negate (forall (P : Power Universe), Sigma y P -> P (Tau (Sigma y))).
Definition Omega :=
  Tau (fun (P : Power Universe) => forall (X : Universe), Sigma X P -> P X).

Definition bad := (
  fun (
    Zero :
      forall (P : Power Universe),
        (forall (X : Universe), Sigma X P -> P X) -> P Omega
  ) => (
    Zero Delta (
      fun (X : Universe) =>
        fun (Two : Sigma X Delta) =>
          fun (
            Three :
              forall (P : Power Universe), Sigma X P -> P (Tau (Sigma X))
          ) => Three Delta Two (
            fun (P : Power Universe) =>
              Three (fun (y : Universe) => P (Tau (Sigma y)))
          )
    )
  ) (
    fun (P : Power Universe) => Zero (fun (y : Universe) => P (Tau (Sigma y)))
  )
) (
  fun (P : Power Universe) =>
    fun (One : forall (X : Universe), Sigma X P -> P X) =>
      One Omega (fun (X : Universe) => One (Tau (Sigma X)))
).

Check bad. (* `ExFalso` *)
Check bad False. (* `False` *)

(*
  ```
  Compute bad.
  Compute bad False.
  ```
*)

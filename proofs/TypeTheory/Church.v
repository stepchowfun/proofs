(*****************************************************************************)
(*****************************************************************************)
(****                                                                     ****)
(****   A demonstration of why Church encodings don't support dependent   ****)
(****   elimination                                                       ****)
(****                                                                     ****)
(*****************************************************************************)
(*****************************************************************************)

(* Non-dependent pairs with non-dependent elimination ("NN") work fine. *)

Definition PairNN (X Y : Type) : Type :=
  forall Z, (X -> Y -> Z) -> Z.

Definition constructNN (X Y : Type) : X -> Y -> PairNN X Y :=
  fun x y Z f => f x y.

Definition elimNN (X Y Z : Type) : (X -> Y -> Z) -> PairNN X Y -> Z :=
  fun f p => p Z f.

Definition firstNN (X Y : Type) : PairNN X Y -> X :=
  fun p => elimNN X Y X (fun x _ => x) p.

Definition secondNN (X Y : Type) : PairNN X Y -> Y :=
  fun p => elimNN X Y Y (fun _ y => y) p.

Compute firstNN bool nat (constructNN bool nat true 42).
Compute secondNN bool nat (constructNN bool nat true 42).

(*
  Dependent pairs with non-dependent elimination ("DN") are also fine, though
  we can't define the second projection in full generality.
*)

Definition PairDN (X : Type) (Y : X -> Type) : Type :=
  forall (Z : Type), (forall x, Y x -> Z) -> Z.

Definition constructDN (X : Type) (Y : X -> Type) :
  forall (x : X), Y x -> PairDN X Y
:=
  fun x y Z f => f x y.

Definition elimDN (X : Type) (Y : X -> Type) (Z : Type) :
  (forall (x : X), Y x -> Z) -> PairDN X Y -> Z
:=
  fun f p => p Z f.

Definition firstDN (X : Type) (Y : X -> Type) : PairDN X Y -> X :=
  fun p => elimDN X Y X (fun x _ => x) p.

(*
  Definition secondDN (X : Type) (Y : X -> Type) : PairDN X Y -> Y ? :=
    fun p => elimDN X Y (Y ?) (fun _ y => y) p.
*)

  Definition secondDN' (X : Type) (Y : Type) : PairDN X (fun _ => Y) -> Y :=
    fun p => elimDN X (fun _ => Y) Y (fun _ y => y) p.

Compute firstDN bool (fun _ => nat) (constructDN bool (fun _ => nat) true 42).
Compute secondDN' bool nat (constructDN bool (fun _ => nat) true 42).

(*
  However, we can't even define the type former for non-dependent pairs with
  dependent elimination ("ND").
*)

(*
  Definition PairND (X Y : Type) : Type :=
    forall (Z : PairND X Y -> Type),
    (forall (x : X) (y : Y), Z (constructND X Y x y)) ->
    Z ?.
*)

(* Dependent pairs with dependent elimination ("DD") have the same problem. *)

(*
  Definition PairDD (X : Type) (Y : X -> Type) : Type :=
    forall (Z : PairDD X Y -> Type),
    (forall (x : X) (y : Y x), Z (constructDD X Y x y)) ->
    Z ?.
*)

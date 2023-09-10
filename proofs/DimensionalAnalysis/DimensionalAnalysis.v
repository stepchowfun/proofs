(**********************************)
(**********************************)
(****                          ****)
(****   Dimensional analysis   ****)
(****                          ****)
(**********************************)
(**********************************)

Require Import Main.Tactics.

Record quantigory := {
  (*
    It's a Cartesian closed category where the objects, called *units*, are
    indexed by *dimensions*.
  *)

  dimension : Type;
  unit : dimension -> Type;
  hom : forall {d1 d2}, unit d1 -> unit d2 -> Type;
  id : forall {d} (u : unit d), hom u u;
  compose :
    forall
      {d1 d2 d3} {u1 : unit d1} {u2 : unit d2} {u3 : unit d3}
      (a1 : hom u1 u2) (a2 : hom u2 u3), hom u1 u3;
  
  leftIdentity :
    forall {d1 d2} {u1 : unit d1} {u2 : unit d2} (a : hom u1 u2),
    compose (id u1) a = a;
  rightIdentity :
    forall {d1 d2} {u1 : unit d1} {u2 : unit d2} (a : hom u1 u2),
    compose a (id u2) = a;
  associativity :
    forall
    {d1 d2 d3 d4}
    {u1 : unit d1} {u2 : unit d2} {u3 : unit d3} {u4 : unit d4}
    (a1 : hom u1 u2) (a2 : hom u2 u3) (a3 : hom u3 u4),
    compose (compose a1 a2) a3 = compose a1 (compose a2 a3);

  terminalDimension : dimension;
  terminalUnit : unit terminalDimension;

  productDimension : dimension -> dimension -> dimension;
  productUnit :
    forall {d1 d2} (u1 : unit d1) (u2 : unit d2),
    unit (productDimension d1 d2);

  exponentialDimension : dimension -> dimension -> dimension;
  exponentialUnit :
    forall {d1 d2} (u1 : unit d1) (u2 : unit d2),
    unit (exponentialDimension d1 d2);

  (*
    For every dimension, there are unique conversions between units for that
    dimension.
  *)

  convert : forall {d} (u1 u2 : unit d), hom u1 u2;

  convertIdentity : forall d (u : unit d), convert u u = id u;
  convertCoherent :
    forall {d} (u1 u2 u3 : unit d),
    compose (convert u1 u2) (convert u2 u3) = convert u1 u3;

  (* Quantities of the same units can be added. *)

  add : forall {d} {u : unit d}, hom (productUnit u u) u;

  (* Conversions are linear. *)

  (*
    add (convert x) (convert y) = convert (add x y)

  distribution :
    forall {d} {u1 u2 : unit d},
    convert u1 u2
  *)

  (* Hom sets hom(X, X) are isomorphic??? *)

  cancellation :
    forall {d1 d2} {u1 : unit d1} {u2 : unit d2},
    hom u1 u1 -> hom u2 u2;

  metaCancellation1 :
    forall {d1 d2} {u1 : unit d1} {u2 : unit d2},
    cancellation (id u1) = id u2;

  metaCancellation2 :
    forall
      {d1 d2 d3}
      {u1 : unit d1} {u2 : unit d2} {u3 : unit d3}
      (a : hom u1 u1),
    @cancellation d2 d3 u2 u3 (cancellation a) = cancellation a;
}.

Inductive exampleDimension := terminal | length | duration.

Inductive exampleUnit : exampleDimension -> Type :=
| empty : exampleUnit terminal
| product : exampleUnit terminal
| meter : exampleUnit length
| kilometer : exampleUnit length
| second : exampleUnit duration
| hour : exampleUnit duration.

Program Definition exampleQuantigory : quantigory := {|
  dimension := exampleDimension;
  unit := exampleUnit;
  hom _ _ _ _ := nat -> nat;
  id _ _ := fun x => x;
  compose _ _ _ _ _ _ a1 a2 := fun x => a2 (a1 x);
  terminalDimension := terminal;
|}.
Next Obligation.

Print exampleQuantigory.
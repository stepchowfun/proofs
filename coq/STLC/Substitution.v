(**************************)
(**************************)
(****                  ****)
(****   Substitution   ****)
(****                  ****)
(**************************)
(**************************)

Require Import Main.STLC.Name.
Require Import Main.STLC.Syntax.

Fixpoint sub e1 x1 e2 :=
  match e1 with
  | eTrue => e1
  | eFalse => e1
  | eIf e3 e4 e5 => eIf (sub e3 x1 e2) (sub e4 x1 e2) (sub e5 x1 e2)
  | eVar x2 => if nameEq x1 x2 then e2 else e1
  | eAbs x2 t e3 => if nameEq x1 x2 then e1 else eAbs x2 t (sub e3 x1 e2)
  | eApp e3 e4 => eApp (sub e3 x1 e2) (sub e4 x1 e2)
  end.

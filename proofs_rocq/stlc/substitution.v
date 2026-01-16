(**************************)
(**************************)
(****                  ****)
(****   Substitution   ****)
(****                  ****)
(**************************)
(**************************)

Require Import main.stlc.name.
Require Import main.stlc.syntax.

Fixpoint sub e1 x1 e2 :=
  match e1 with
  | e_true => e1
  | e_false => e1
  | e_if e3 e4 e5 => e_if (sub e3 x1 e2) (sub e4 x1 e2) (sub e5 x1 e2)
  | e_var x2 => if name_eq x1 x2 then e2 else e1
  | e_abs x2 t e3 => if name_eq x1 x2 then e1 else e_abs x2 t (sub e3 x1 e2)
  | e_app e3 e4 => e_app (sub e3 x1 e2) (sub e4 x1 e2)
  end.

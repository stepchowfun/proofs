(*****************************)
(*****************************)
(****                     ****)
(****   Helpful tactics   ****)
(****                     ****)
(*****************************)
(*****************************)

Require Import Omega.

(* This tactic removes superfluous hypotheses. *)

Ltac clean := repeat (
  match goal with
  | [ H : ?x = ?y |- _ ] => (is_var y; subst x) || (is_var x; subst y)
  | [ H : ?x = ?x |- _ ] => clear H
  end
).

(*
  This tactic tries a variety of approaches to solve a goal. It uses the
  resolve, rewrite, and unfold hints from the "core" database.
*)

Ltac magic := try abstract (
  clean;
  cbn;
  intros;
  f_equal;
  idtac + autounfold with core in *;
  idtac + autorewrite with core in *;
  omega + congruence + dintuition
).

(*
  This tactic is useful if you have a hypothesis H : P -> Q and you want to
  use Q. You can just write `feed H`. A new proof obligation for P will be
  generated, and then the hypothesis will be specialized to H : Q.
*)

Ltac feed H1 := let H2 := fresh "H" in
  match type of H1 with
  | ?T -> _ => assert (H2 : T); [ | specialize (H1 H2); clear H2 ]
  end.

(*
  This tactic takes a given term and adds its type to the context as a new
  hypothesis.
*)

Ltac fact E := let H := fresh "H" in pose (H := E); clearbody H.

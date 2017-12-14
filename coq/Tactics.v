(*****************************)
(*****************************)
(****                     ****)
(****   Helpful tactics   ****)
(****                     ****)
(*****************************)
(*****************************)

Require Import Omega.

(*
  This tactic tries a variety of approaches to solve a goal. It uses the
  resolve, rewrite, and unfold hints from the "core" database.
*)

Ltac magic := try solve [
  idtac + intros;
  idtac + cbn;
  idtac + f_equal;
  idtac + autounfold with core in *;
  idtac + autorewrite with core in *;
  omega + congruence + dintuition eauto with *
].

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

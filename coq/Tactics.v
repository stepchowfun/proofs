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
  resolve hints from all databases and the rewrite hints from the "core"
  database.
*)

Ltac magic :=
  let simplify := repeat (
    cbn in *;
    intros;
    try subst;
    try (autorewrite with core in *);
    repeat (
      match goal with
      | [ H : ex _ |- _ ] => destruct H
      end
    )
  ) in let discharge :=
    try (
      match goal with
      | [ H : _ |- _ ] => inversion H; fail
      end
    );
    auto with *;
    try abstract (dintuition (simplify; auto with *));
    try congruence;
    try omega;
    eauto with *;
    dintuition (simplify; eauto with *)
  in try abstract (
    simplify;
    idtac + f_equal;
    simplify;
    discharge
  ).

(*
  This tactic takes a given term and adds it to the context as a new
  hypothesis.
*)

Ltac fact E := let H := fresh "H" in pose (H := E); clearbody H.

(*
  This tactic is useful if you have a hypothesis H : P -> Q and you want to
  use Q. You can just write `feed H`. A new proof obligation for P may be
  generated, and then the hypothesis will be specialized to H : Q.
*)

Ltac feed H1 := let H2 := fresh "H" in
  match type of H1 with
  | ?T -> _ => assert (H2 : T); [ | specialize (H1 H2); clear H2 ]
  end; magic.

(* This is like the `inversion` tactic, but leaves less junk around. *)

Ltac invert H := inversion H; clear H; try subst.

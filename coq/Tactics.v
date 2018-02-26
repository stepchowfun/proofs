(*****************************)
(*****************************)
(****                     ****)
(****   Helpful tactics   ****)
(****                     ****)
(*****************************)
(*****************************)

Require Import Omega.

(* This tactic does a variety of simplifications on the goal and hypotheses. *)

Ltac simplify :=
  let rec reorderContext :=
    try match goal with
    | [ H : ?T |- _ ] =>
      match type of T with
        | context[Prop] => revert H; reorderContext; intro H
      end
    | [ H : context[Prop] |- _ ] => revert H; reorderContext; intro H
    end
  in repeat (
    intros;
    cbn in *;
    subst;
    try (autorewrite with core in *);
    repeat (
      match goal with
      | [ H : ex _ |- _ ] => destruct H
      end
    )
  ); reorderContext.

(*
  The `magic` tactic tries a variety of approaches to solve a goal. It uses the
  resolve hints from all databases and the rewrite hints from the "core"
  database. The `eMagic` tactic does everything `magic` does but uses `eauto`
  instead of `auto`.
*)

Ltac magicWith tactic :=
  try abstract (
    simplify;
    try abstract (
      match goal with
      | [ H : _ |- _ ] => inversion H; fail
      end
    );
    try abstract tactic;
    try abstract (dintuition (simplify; tactic));
    try abstract (progress f_equal; magicWith tactic);
    try abstract congruence;
    try abstract omega
  ).

Ltac magic := let autoStar := auto with * in magicWith autoStar.

Ltac eMagic := let eautoStar := eauto with * in magicWith eautoStar.

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

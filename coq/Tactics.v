(*************************************)
(*************************************)
(****                             ****)
(****   General-purpose tactics   ****)
(****                             ****)
(*************************************)
(*************************************)

Require Import Omega.

(*
  This tactic does a variety of simplifications on the goal and hypotheses.
  It's used by the `magic` tactics below. If you just want to clean up the goal
  and context for easier reading, use the `clean` tactic below.
*)

Ltac simplify tactic :=
  repeat (
    intros;
    cbn in *;
    subst;
    try (autorewrite with core in *);
    try (
      match goal with
      | [ H : ex _ |- _ ] => destruct H
      | [ H : _ /\ _ |- _ ] => destruct H
      | [ H : _ <-> _ |- _ ] => destruct H
      | [ H : ?T = ?T |- _ ] => clear H
      | [ H1 : ?T -> _ |- _ ] =>
        match type of T with
        | context[Prop] =>
          let H2 := fresh "H"
          in assert (H2 : T); [
            solve [ tactic ] |
            specialize (H1 H2); clear H2
          ]
        end
      end
    )
  ).

(*
  The `magic` tactic tries a variety of approaches to solve a goal. The
  `eMagic` tactic does everything `magic` does but uses `eauto` instead of
  `auto`.
*)

Ltac magicWith tactic :=
  try solve [tactic];
  try solve [
    simplify tactic;
    try solve [dintuition (simplify tactic; tactic)];
    try solve [progress f_equal; magicWith tactic];
    try solve [congruence];
    try solve [omega];
    try solve [
      match goal with
      | [ |- context[if ?X then _ else _] ] =>
        destruct X; magicWith tactic; fail
      | [ _ : context[if ?X then _ else _] |- _ ] =>
        destruct X; magicWith tactic; fail
      | [ H : _ |- _ ] => inversion H; fail
      end
    ]
  ].

Tactic Notation "magic" integer(n) :=
  let autoStar := auto n with * in magicWith autoStar.

Tactic Notation "magic" := magic 5.

Tactic Notation "eMagic" integer(n) :=
  let eautoStar := eauto n with * in magicWith eautoStar.

Tactic Notation "eMagic" := eMagic 5.

(*
  This tactic reorders the context such that definitions come before
  assumptions.
*)

Ltac sort :=
  try match goal with
  | [ H : ?T |- _ ] =>
    match type of T with
    | context[Prop] => revert H; sort; intro H
    end
  | [ H : context[Prop] |- _ ] => revert H; sort; intro H
  end.

(* This tactic cleans up the goal and context for easier reading. *)

Ltac clean := let magicTactic := magic in simplify magicTactic; sort.

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

Ltac feed H1 :=
  let H2 := fresh "H"
  in
    match type of H1 with
    | ?T -> _ => assert (H2 : T); [ | specialize (H1 H2); clear H2 ]
    end; magic.

(* This notation performs `generalize dependent` on multiple terms at once. *)

Tactic Notation "gen" constr(e1) :=
  generalize dependent e1.

Tactic Notation "gen" constr(e1) constr(e2) :=
  generalize dependent e2;
  generalize dependent e1.

Tactic Notation "gen" constr(e1) constr(e2) constr(e3) :=
  generalize dependent e3;
  generalize dependent e2;
  generalize dependent e1.

Tactic Notation "gen" constr(e1) constr(e2) constr(e3) constr(e4) :=
  generalize dependent e4;
  generalize dependent e3;
  generalize dependent e2;
  generalize dependent e1.

Tactic Notation "gen" constr(e1) constr(e2) constr(e3) constr(e4) constr(e5) :=
  generalize dependent e5;
  generalize dependent e4;
  generalize dependent e3;
  generalize dependent e2;
  generalize dependent e1.

(* This is like the `inversion` tactic, but leaves less junk around. *)

Ltac invert H := inversion H; try clear H; subst.

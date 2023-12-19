(*************************************)
(*************************************)
(****                             ****)
(****   General-purpose tactics   ****)
(****                             ****)
(*************************************)
(*************************************)

Require Import Coq.micromega.Lia.

(* Ensure this hint database exists. *)

Create HintDb main.

(*
  This tactic does a variety of simplifications on the goal and hypotheses.
  It's used by the `search` tactics below. If you just want to clean up the
  goal and context for easier reading, use the `clean` tactic below.
*)

#[local] Ltac simplify tactic :=
  repeat (
    intros;
    subst;
    cbn in *;
    try match goal with
        | [H : ?T = ?T |- _] => clear H
        | [H : ex _ |- _] => destruct H
        | [H : _ /\ _ |- _] => destruct H
        | [H : _ <-> _ |- _] => destruct H
        | [H1 : ?T -> _ |- _] =>
          match type of T with
          | Prop =>
            let H2 := fresh "H" in
            assert (H2 : T); [
              solve [tactic] |
              specialize (H1 H2); clear H2
            ]
          end
        end
  ).

(*
  The `search` tactic tries a variety of approaches to solve a goal. The
  `esearch` tactic does everything `search` does but uses `eauto` instead of
  `auto`.
*)

#[local] Ltac search_with tactic :=
  try solve [tactic];
  try solve [
    simplify tactic;
    try autorewrite with main in *;
    try autounfold with main in *;
    try solve [congruence];
    try solve [constructor; search_with tactic];
    try solve [dintuition (simplify tactic; tactic)];
    try solve [lia];
    try solve [progress f_equal; search_with tactic];
    try solve [
      match goal with
      | [X : unit |- _] => destruct X; search_with tactic; fail
      | [|- context[if ?X then _ else _]] =>
        destruct X; search_with tactic; fail
      | [_ : context[if ?X then _ else _] |- _] =>
        destruct X; search_with tactic; fail
      | [H : _ |- _] => inversion H; fail
      end
    ]
  ].

Tactic Notation "search" integer(n) :=
  let auto_tactic := auto n with arith datatypes main
  in search_with auto_tactic.

Tactic Notation "search" := search 5.

Tactic Notation "esearch" integer(n) :=
  let eauto_tactic := eauto n with arith datatypes main
  in search_with eauto_tactic.

Tactic Notation "esearch" := esearch 5.

#[export] Obligation Tactic := search.

(*
  This tactic reorders the context such that definitions come before
  assumptions.
*)

Ltac sort :=
  try match goal with
  | [H : ?T |- _] =>
    match type of T with
    | context[Prop] => revert H; sort; intro H
    end
  | [H : context[Prop] |- _] => revert H; sort; intro H
  end.

(* This tactic cleans up the goal and context for easier reading. *)

Ltac clean := let search_tactic := search in simplify search_tactic; sort.

(*
  This tactic is useful if you have a hypothesis `H : P -> Q` and you want to
  use `Q`. You can just write `feed H`. A new proof obligation for `P` may be
  generated, and then the hypothesis will be specialized to `H : Q`.
*)

Ltac feed H1 :=
  let H2 := fresh "H"
  in
    match type of H1 with
    | ?T -> _ => assert (H2 : T); [| specialize (H1 H2); clear H2]
    end; search.

(* This notation performs `revert dependent` on multiple terms at once. *)

Tactic Notation "outro" constr(e1) :=
  revert dependent e1.

Tactic Notation "outro" constr(e1) constr(e2) :=
  revert dependent e2;
  revert dependent e1.

Tactic Notation "outro" constr(e1) constr(e2) constr(e3) :=
  revert dependent e3;
  revert dependent e2;
  revert dependent e1.

Tactic Notation "outro" constr(e1) constr(e2) constr(e3) constr(e4) :=
  revert dependent e4;
  revert dependent e3;
  revert dependent e2;
  revert dependent e1.

Tactic Notation "outro"
  constr(e1)
  constr(e2)
  constr(e3)
  constr(e4)
  constr(e5)
:=
  revert dependent e5;
  revert dependent e4;
  revert dependent e3;
  revert dependent e2;
  revert dependent e1.

(* This is like the `inversion` tactic, but leaves less junk around. *)

Ltac invert H := inversion H; clear H; subst.

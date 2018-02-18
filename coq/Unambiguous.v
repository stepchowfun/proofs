(***********************************************************)
(***********************************************************)
(****                                                   ****)
(****   A proof that a simple grammar is unambiguous.   ****)
(****                                                   ****)
(***********************************************************)
(***********************************************************)

Require Import Coq.Lists.List.
Require Import Main.Tactics.

Import ListNotations.

Inductive token :=
| tConst : nat -> token
| tPlus : token.

Inductive term :=
| eConst : nat -> term
| eSum : nat -> term -> term.

Fixpoint print (e : term) :=
  match e with
  | eConst n => [ tConst n ]
  | eSum n e => [ tConst n ] ++ [ tPlus ] ++ print e
  end.

Theorem unambiguous : forall e1 e2, print e1 = print e2 -> e1 = e2.
Proof.
  intros.
  generalize dependent e2.
  induction e1; intros; destruct e2; cbn in H; inversion H; magic.
Qed.

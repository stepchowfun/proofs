(**********************************)
(**********************************)
(****                          ****)
(****   The progress theorem   ****)
(****                          ****)
(**********************************)
(**********************************)

Require Import main.system_f.context.
Require Import main.system_f.opening.
Require Import main.system_f.semantics.
Require Import main.system_f.syntax.
Require Import main.system_f.typing.
Require Import main.tactics.

Theorem progress :
  forall e1 t,
  HasType c_empty e1 t ->
  Value e1 \/ exists e2, Step e1 e2.
Proof.
  clean. remember c_empty. pose proof (typing_regularity c e1 t H).
  induction H; search; right; clean.
  - pose proof (typing_regularity c_empty e2 t2 H1).
    pose proof (typing_regularity c_empty e1 (t_arrow t2 t1) H).
    clean.
    destruct IHHasType1; destruct IHHasType2; esearch.
    invert H; esearch.
  - pose proof (typing_regularity c_empty e (t_for_all t1) H1).
    clean.
    destruct IHHasType; clean.
    + invert H1; search. exists (et_open e0 0 t2). invert H. search.
    + exists (e_t_app x t2). invert H. search.
Qed.

Hint Resolve progress : main.

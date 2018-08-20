(*************************************************)
(*************************************************)
(****                                         ****)
(****   Encoding logic with dependent types   ****)
(****                                         ****)
(*************************************************)
(*************************************************)

(* A proposition which is trivially provable *)

Inductive True : Prop :=
| trivial : True.

(* A proposition which is not provable *)

Inductive False : Prop := .

(* Logical conjunction *)

Inductive and P Q : Prop := (* Notation: P /\ Q *)
| conj : P -> Q -> and P Q.

(* A proof of True AND True *)

Definition true_and_true_1 : and True True :=
  conj True True trivial trivial.

(* The same proof, but written in "proof mode" *)

Theorem true_and_true_2 : and True True.
Proof.
  (* Our first example of a tactic: apply *)
  apply conj.
  - apply trivial.
  - apply trivial.
Qed.

Print true_and_true_2.

(* The same proof, but written using the `;` tactical *)

Theorem true_and_true_3 : and True True.
Proof.
  (* Our first example of a tactic: apply. *)
  apply conj; apply trivial.
Qed.

(* Let's see what happens when we try to prove True AND False. *)

Theorem true_and_false : and True False.
Proof.
  apply conj.
  - apply trivial.
  - (* Stuck here... *)
Abort.

(* If and only if *)

Definition iff P Q := and (P -> Q) (Q -> P). (* Notation: P <-> Q *)

(* Logical disjunction *)

Inductive or P Q : Prop := (* Notation: P \/ Q *)
| orIntroL : P -> or P Q
| orIntroR : Q -> or P Q.

(* Let's prove True OR False. *)

Theorem true_or_false : or True False.
Proof.
  left. (* Equivalent to `apply orIntroL.` *)
  apply trivial.
Qed.

(* Logical negation *)

Definition not A := A -> False. (* Notation: ~ A *)

(* A proof of NOT False *)

Theorem not_false : not False.
Proof.
  (* `unfold` replaces a name with its definition. *)
  unfold not.

  (* `intro` moves a premise of the goal into the context. *)
  intro.

  (* H is a proof of the goal; let's use it! *)
  exact H.
Qed.

Print not_false.

(* Propositional equality *)

Inductive eq (A : Type) (x : A) : A -> Prop := (* Notation: x = x *)
| eq_refl : eq A x x. (* A dependent type! *)

(* A simple proof that 0 = 0. *)
Theorem zero_eq_zero : eq nat 0 0.
Proof.
  reflexivity. (* Equivalent to: `apply eq_refl.` *)
Qed.

(*
  Here we show that this definition of propositional equality is "Leibniz
  equaltiy".
*)

Definition leibniz (A : Type)
                   (x : A)
                   (P : A -> Prop)
                   (f : P x)
                   (y : A)
                   (e : eq A x y) :
                   P y :=
  match e in eq _ _ z return P z with (* Here, z = y. *)
  | eq_refl _ _ => f (* But z = x here. *)
  end.

(*
  And guess what: the above definition of `leibniz` is automatically generated
  for us as the induction principle for `eq`.
*)

Check leibniz.
Check eq_ind.

(*
  Universal quantification (forall) is built into the language. Existential
  quantification, however, is definable as follows:
*)

Inductive ex (A : Type)
             (P : A -> Prop) :
             Prop := (* Notation: exists x, P x *)
  ex_intro : forall x : A, P x -> ex A P.

(* A simple existence proof *)

Theorem reflexive_value_exists : ex nat (fun x => x = x).
Proof.
  exists 0. (* Equivalent to `apply ex_intro with (x := 0).` *)
  reflexivity.
Qed.

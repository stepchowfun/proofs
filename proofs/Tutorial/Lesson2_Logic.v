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

Inductive and P Q : Prop := (* Notation: `P /\ Q` *)
| conj : P -> Q -> and P Q.

(* Make the `P` and `Q` arguments of conj implicit. *)

Arguments conj {_} {_}.

(* A proof of `True` *and* `True` *)

Definition true_and_true_1 : and True True :=
  conj trivial trivial.

(* The same proof, but written in "proof mode" *)

Theorem true_and_true_2 : and True True.
Proof.
  (* Our first example of a tactic: `apply` *)
  apply conj.
  - apply trivial.
  - apply trivial.
Qed.

Print true_and_true_2. (* `conj trivial trivial` *)

(* The same proof, but written using the `;` tactical *)

Theorem true_and_true_3 : and True True.
Proof.
  apply conj; apply trivial.
Qed.

Print true_and_true_3. (* `conj trivial trivial` *)

(* Let's see what happens when we try to prove `True` *and* `False`. *)

Theorem true_and_false : and True False.
Proof.
  apply conj.
  - apply trivial.
  - (* Stuck here... *)
Abort.

(* If and only if *)

Definition iff P Q := and (P -> Q) (Q -> P). (* Notation: `P <-> Q` *)

(* Logical disjunction *)

Inductive or P Q : Prop := (* Notation: `P \/ Q` *)
| orIntroL : P -> or P Q
| orIntroR : Q -> or P Q.

(* Make the `P` and `Q` arguments of `orIntroL` and `orIntroR` implicit. *)

Arguments orIntroL {_} {_}.
Arguments orIntroR {_} {_}.

(* Let's prove `True` *or* `False`. *)

Theorem true_or_false : or True False.
Proof.
  left. (* Equivalent to `apply orIntroL.` *)
  apply trivial.
Qed.

(* Logical negation *)

Definition not A := A -> False. (* Notation: ~ A *)

(* A proof of *not* `False` *)

Theorem not_false : not False.
Proof.
  (* `unfold` replaces a name with its definition. *)
  unfold not.

  (* `intro` moves a premise of the goal into the context. *)
  intro.

  (* H is a proof of the goal; let's use it! *)
  exact H.
Qed.

Print not_false. (* `fun H : False => H` *)

(* Propositional equality *)

Inductive eq A (x : A) : A -> Prop := (* Notation: `x = x` *)
| eq_refl : eq A x x. (* A dependent type! *)

(* Make the `A` argument of `eq_refl` implicit. *)

Arguments eq_refl {_}.

(* A simple proof that 0 = 0. *)
Theorem zero_eq_zero : eq nat 0 0.
Proof.
  reflexivity. (* Equivalent to: `apply eq_refl.` *)
Qed.

(*
  Here we show that this definition of propositional equality is "Leibniz
  equality".
*)

Definition leibniz A
                   (x : A)
                   (P : A -> Prop)
                   (f : P x)
                   (y : A)
                   (e : eq A x y) :
                   P y :=
  match e in eq _ _ z return P z with (* Here, `z` = `y`. *)
  | eq_refl _ => f (* But `z` = `x` here. *)
  end.

(*
  And guess what: the above definition of `leibniz` is automatically generated
  for us as the induction principle for `eq`.
*)

Check leibniz.

(*
  ```
  forall (A : Type) (x : A) (P : A -> Prop),
  P x -> forall y : A, eq A x y -> P y
  ```
*)

Check eq_ind.

(*
  ```
  forall (A : Type) (x : A) (P : A -> Prop),
  P x -> forall y : A, eq A x y -> P y
  ```
*)

(*
  Universal quantification (`forall`) is built into the language. Existential
  quantification, however, is definable as follows:
*)

Inductive ex A (P : A -> Prop) : Prop := (* Notation: `exists x, P x` *)
  ex_intro : forall x : A, P x -> ex A P.

(* Make the `A` and `P` arguments of `ex_intro` implicit. *)

Arguments ex_intro {_} {_}.

(* A simple existence proof *)

Theorem reflexive_value_exists : ex nat (fun x => x = x).
Proof.
  exists 0. (* Equivalent to `apply ex_intro with (x := 0).` *)
  reflexivity.
Qed.

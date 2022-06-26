(*************************************************)
(*************************************************)
(****                                         ****)
(****   Encoding logic with dependent types   ****)
(****                                         ****)
(*************************************************)
(*************************************************)

(*
  Consider a mathematical statement you'd like to prove. An example of such a
  proposition might be that addition of natural numbers is commutative. In Coq,
  we'd represent that proposition as a type:

  ```
  forall x y, x + y = y + x
  ```

  This type might seem strange at first. You already know about `forall` and
  `+`, but we haven't seen `=` yet. Fear not! In this lesson, we'll see how
  this notion of equality and other logical constructs like "and" and "or" can
  be defined as type families in Coq.

  How then can we prove a proposition like that? In Coq, we prove a proposition
  by constructing an element of the corresponding type. So a proof corresponds
  to a program, and the proposition it proves corresponds to the type of that
  program. This idea is called *propositions as types*.

  It'll be useful to define a proposition which is trivially true. We'll call
  this proposition `True`, but don't mistake it for a `bool`! As explained
  above, propositions like `True` correspond to types.
*)

Inductive True : Prop :=
| I : True.

(*
  So `True` is a proposition, and `I` is its proof. This is a bit abstract, but
  it'll become more clear once we define a few other logical concepts.

  Note that we put `True` in a universe called `Prop` instead of `Set`. In
  general, propositions will live in `Prop`. This is an easy way to distinguish
  proofs from programs, and it'll allow Coq to erase all the proofs when
  extracting the code into another programming language. See Lesson 5 for
  details about universes and Lesson 6 for details about program extraction.

  It'll also be useful to have a proposition which is trivially false. We'll
  call that proposition `False`:
*)

Inductive False : Prop := .

(*
  Note that `False` has no constructors, and therefore no proofs!

  One of the most familiar logical concepts is *conjunction*, also known as
  "and". To prove "P and Q", we need to provide a proof of "P" and a proof of
  "Q". We can define this in Coq as follows:
*)

Inductive and (P Q : Prop) : Prop := (* Notation: `P /\ Q` *)
| conj : P -> Q -> and P Q.

Arguments conj {_} {_} _ _.

(* Here's a proof of `True` *and* `True` *)

Definition true_and_true_1 : and True True := conj I I.

(*
  Writing proofs by hand can be extremely tedious in practice. Coq has a
  scripting language called *Ltac* to help us construct proofs. We can use Ltac
  in *proof mode*. Here is the same proof as above, but written in Ltac using
  proof mode:
*)

Theorem true_and_true_2 : and True True.
Proof.
  (* Our first example of a tactic: `apply` *)
  apply conj.
  - apply I.
  - apply I.
Qed.

Print true_and_true_2. (* `conj I I` *)

(*
  The proof above had two subgoals, and both were solved by `apply I`. In
  situations like that, we can use the `;` tactical to reduce duplication:
*)

Theorem true_and_true_3 : and True True.
Proof.
  apply conj; apply I.
Qed.

Print true_and_true_3. (* `conj I I` *)

(* Let's see what happens when we try to prove `True` *and* `False`. *)

Theorem true_and_false : and True False.
Proof.
  apply conj.
  - apply I.
  - (* Stuck here... *)
Abort.

(* If and only if *)

Definition iff (P Q : Prop) := and (P -> Q) (Q -> P). (* Notation: `P <-> Q` *)

(* Logical disjunction *)

Inductive or (P Q : Prop) : Prop := (* Notation: `P \/ Q` *)
| orIntroL : P -> or P Q
| orIntroR : Q -> or P Q.

Arguments orIntroL {_} {_} _.
Arguments orIntroR {_} {_} _.

(* Let's prove `True` *or* `False`. *)

Theorem true_or_false : or True False.
Proof.
  left. (* Equivalent to `apply orIntroL.` *)
  apply I.
Qed.

(* Logical negation *)

Definition not (A : Prop) := A -> False. (* Notation: `~ A` *)

(* A proof of *not* `False` *)

Theorem not_false : not False.
Proof.
  (* `unfold` replaces a name with its definition. *)
  unfold not.

  (* `intro` moves a premise of the goal into the context. *)
  intro.

  (* `H` is a proof of the goal; let's use it! *)
  exact H.
Qed.

Print not_false. (* `fun H : False => H` *)

(* Propositional equality *)

Inductive eq {A} (x : A) : A -> Prop := (* Notation: `x = x` *)
| eq_refl : eq x x.

(* A simple proof that 0 = 0. *)

Theorem zero_eq_zero : eq 0 0.
Proof.
  reflexivity. (* Equivalent to: `apply eq_refl.` *)
Qed.

(*
  We saw in previous lessons how to do pattern matching and recursion. Coq
  automatically generates an *induction principle* for every inductive data
  type, and using it is equivalent to pattern matching and recursing (if
  applicable) on that type. Let's check the induction principle for `eq`:
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

Arguments ex_intro {_} {_} _ _.

(* A simple existence proof *)

Theorem half_of_4_exists : ex nat (fun x => eq (x + x) 4).
Proof.
  exists 2. (* Equivalent to `apply ex_intro with (x := 2).` *)
  reflexivity.
Qed.

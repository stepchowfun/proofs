(*********************************************************)
(*********************************************************)
(****                                                 ****)
(****   Encoding mathematical propositions as types   ****)
(****                                                 ****)
(*********************************************************)
(*********************************************************)

(*
  In this lesson, we're going to redefine some things from the standard library
  to explain their definitions. We're also going to rebind some notations to
  our definitions, so we silence the relevant warning with this:
*)

#[local] Set Warnings "-notation-overridden".

(*
  Consider a mathematical statement, i.e., a *proposition*, that you'd like to
  prove. An example of a proposition is that addition of natural numbers is
  commutative. In Coq, we'd represent that proposition as a type:

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
  extracting the code to another programming language. See Lesson 5 for details
  about universes and Lesson 6 for details about program extraction.

  Along the same lines as `True`, it'll also be useful to have a proposition
  which is trivially false:
*)

Inductive False : Prop := .

(*
  Note that `False` has no constructors and therefore no proofs!

  One of the most familiar logical concepts is *conjunction*, also known as
  "and". To prove "A and B", we need to provide a proof of "A" and a proof of
  "B". We can define this in Coq as follows:
*)

Inductive and (A B : Prop) : Prop :=
| conj : A -> B -> and A B.

Arguments conj {_} {_} _ _.

(*
  The following specifies that the notation `A /\ B` will be used as shorthand
  for `and A B`. The `type_scope` notation scope indicates that this notation
  only applies in contexts where a type is expected.
*)

Notation "A /\ B" := (and A B) : type_scope.

(* Let's write a proof! *)

Definition true_and_true_1 : True /\ True := conj I I.

(*
  Writing proofs by hand can be extremely tedious in practice. Coq has a
  scripting language called *Ltac* to help us construct proofs. We can use Ltac
  in *proof mode*. Here is the same proof as above, but written in Ltac using
  proof mode:
*)

Theorem true_and_true_2 : True /\ True.
Proof.
  (* Use `split` to prove each half of a conjunction individually. *)
  split.

  (* Use `apply` to prove the goal via some known fact. *)
  - apply I.

  (* Déjà vu! *)
  - apply I.
Qed.

Print true_and_true_2. (* `conj I I` *)

(*
  The proof above had two subgoals, and both were solved by `apply I`. In
  situations like that, we can use the `;` *tactical* to reduce duplication:
*)

Theorem true_and_true_3 : True /\ True.
Proof.
  split; apply I.
Qed.

Print true_and_true_3. (* `conj I I` *)

(* Let's see what happens when we try to prove `True` *and* `False`. *)

Theorem true_and_false : True /\ False.
Proof.
  split.
  - apply I.
  - (* We're stuck here! *)
Abort.

(*
  We don't need to define *implication*, since "A implies B" is just `A -> B`.
  In other words, a proof of "A implies B" is a function which transforms a
  proof of "A" into a proof of "B".
*)

Theorem A_and_B_implies_A : forall A B, A /\ B -> A.
Proof.
  (* `intros` moves the premises of the goal into the context. *)
  intros.

  (*
    If we have a conjunction in the context, we can use `destruct` to get
    access to the two components.
  *)
  destruct H.

  (* The new `H` proves the goal. *)
  apply H.
Qed.

Theorem A_and_B_implies_B : forall A B, A /\ B -> B.
Proof.
  intros.
  destruct H.
  apply H0.
Qed.

Definition explosion_1 (A : Prop) (H: False) : A :=
  match H with
  (* No cases to worry about! *)
  end.

Check explosion_1. (* `forall A : Prop, False -> A` *)

Theorem explosion_2 : forall A : Prop, False -> A.
Proof.
  (* You know the drill. *)
  intros.

  (* We can `destruct` a proof of `False` to prove anything! *)
  destruct H.
Qed.

(*
  To prove the *equivalence* "A if and only if B", we have to prove "A" and "B"
  imply each other.
*)

Definition iff (A B : Prop) := (A -> B) /\ (B -> A).

Notation "A <-> B" := (iff A B) : type_scope.

Theorem A_iff_A : forall A, A <-> A.
Proof.
  intro. (* `intro` is like `intros` but only applies to a single premise. *)
  unfold iff. (* `unfold` replaces a name with its definition. *)
  split; intro; apply H.
Qed.

Theorem A_iff_B_and_A_implies_B : forall A B, (A <-> B) -> A -> B.
Proof.
  intros.
  unfold iff in H. (* Same as before but now in a hypothesis *)
  destruct H.
  apply H. (* If we `apply` an implication, we have to prove its premise(s). *)
  apply H0.
Qed.

(*
  To prove the *disjunction* "A or B", we must provide either a proof of "A" or
  a proof of "B".
*)

Inductive or (A B : Prop) : Prop :=
| orIntroL : A -> or A B
| orIntroR : B -> or A B.

Arguments orIntroL {_} {_} _.
Arguments orIntroR {_} {_} _.

Notation "A \/ B" := (or A B) : type_scope.

Theorem true_or_false : True \/ False.
Proof.
  left. (* Equivalent to `apply orIntroL.` *)
  apply I.
Qed.

Theorem disjunction_symmetric : forall A B, (A \/ B) -> (B \/ A).
Proof.
  intros.
  destruct H. (* `destruct` does case analysis on a disjunctive hypothesis. *)
  - right. (* Equivalent to `apply orIntroR.` *)
    apply H.
  - left.
    apply H.
Qed.

(* In Coq, the *negation* "not A" is defined as "A implies False". *)

Definition not (A : Prop) := A -> False.

Notation "~ x" := (not x) : type_scope.

Theorem not_false : ~False.
Proof.
  unfold not.
  intro.
  apply H.
Qed.

Theorem triple_negation : forall A, ~~~A -> ~A.
Proof.
  unfold not.
  intros.
  apply H.
  intro.
  apply H1.
  apply H0.
Qed.

(* Propositional equality *)

Inductive eq {A} (x : A) : A -> Prop :=
| eq_refl : eq x x.

Notation "x = y" := (eq x y) : type_scope.

Theorem one_plus_one_equals_two : 1 + 1 = 2.
Proof.
  reflexivity. (* Equivalent to: `apply eq_refl.` *)
Qed.

(*
  Universal quantification (`forall`) is built into the language. Existential
  quantification can be defined:
*)

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  ex_intro : forall x : A, P x -> ex P.

Arguments ex_intro {_} {_} _ _.

(*
  The notation for existentials is somewhat tricky to specify. If you're
  curious about the details, consult the Coq reference manual.
*)

Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, right associativity) : type_scope.

Theorem half_of_4_exists : exists x, x + x = 4.
Proof.
  exists 2. (* Equivalent to `apply ex_intro with (x := 2).` *)
  reflexivity.
Qed.

(*************)
(* Exercises *)
(*************)

(*
  1. Prove `False -> True`.
  1. Prove `forall A, A /\ ~A -> False`.
  2. Prove `forall A B, (A /\ B) <-> (B /\ A)`.
  3. Prove `forall A B, (A \/ B) <-> (B \/ A)`.
  4. Prove `forall A B, (A /\ B) -> (A \/ B)`.
  5. Prove `forall x, 3 = x -> x * 2 = 6`.
  6. Prove `exists x, negb x = false`.
*)

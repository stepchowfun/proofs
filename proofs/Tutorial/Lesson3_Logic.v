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
  in *proof mode*. Below is the same proof as above, but written in Ltac using
  proof mode.

  To write proofs using proof mode, it's essential that you're using an IDE
  that supports Coq, such as CoqIDE or Visual Studio Code with the VsCoq
  plugin.
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
    `destruct` implements pattern matching. If we have a proof of `A /\ B`, we
    can `destruct` it to get access to the proofs of `A` and `B`.
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

Definition explosion_1 (A : Prop) (H : False) : A :=
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

Definition A_iff_A_1 A : A <-> A :=
  conj (fun H => H) (fun H => H).

Theorem A_iff_A_2 : forall A, A <-> A.
Proof.
  intros.
  unfold iff. (* `unfold` replaces a name with its definition. *)
  split; intro; apply H.
Qed.

Definition A_iff_B_and_A_implies_B_1 A B (H1 : A <-> B) (H2 : A) : B :=
  match H1 with
  | conj H3 _ => H3 H2
  end.

Theorem A_iff_B_and_A_implies_B_2 : forall A B, (A <-> B) -> A -> B.
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

Definition true_or_false_1 : True \/ False := orIntroL I.

Theorem true_or_false_2 : True \/ False.
Proof.
  left. (* Equivalent to `apply orIntroL.` *)
  apply I.
Qed.

Definition disjunction_symmetric_1 A B (H1 : A \/ B) : (B \/ A) :=
  match H1 with
  | orIntroL H2 => orIntroR H2
  | orIntroR H2 => orIntroL H2
  end.

Theorem disjunction_symmetric_2 : forall A B, (A \/ B) -> (B \/ A).
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

Notation "~ A" := (not A) : type_scope.

Definition not_false_1 : ~False := fun H => H.

Theorem not_false_2 : ~False.
Proof.
  unfold not.
  intros.
  apply H.
Qed.

Definition triple_negation_1 A : ~~~A -> ~A :=
  fun (H1 : ((A -> False) -> False) -> False) (H2 : A) =>
    H1 (fun H3 : A -> False => H3 H2).

Theorem triple_negation_2 : forall A, ~~~A -> ~A.
Proof.
  unfold not.
  intros.
  apply H.
  intros.
  apply H1.
  apply H0.
Qed.

(*
  In Lesson 2, we learned that Coq has a built-in notion of equality which is
  used for type checking: two expressions are considered equal if they compute
  to syntatically identical expressions. This is definitional equality.

  Thus, `0 + n` is definitionally equal to `n`, because `+` pattern matches on
  the `0` and returns `n` in that case. However, `n + 0` is not definitionally
  equal to `n`. How unfortunate!

  We can define a more flexible version of equality as an inductive family.
  This kind of equality isn't as convenient to work with, since the type
  checker can't use it automatically by doing computation. However, it allows
  us to *prove* that `n + 0 = n`, and then we can use such a proof to freely
  substitute one side for the other. This notion of equality which requires
  proof is called *propositional equality*:
*)

Inductive eq {A} (x : A) : A -> Prop :=
| eq_refl : eq x x.

Notation "x = y" := (eq x y) : type_scope.

Definition one_plus_one_equals_two_1 : 1 + 1 = 2 := eq_refl 2.

Theorem one_plus_one_equals_two_2 : 1 + 1 = 2.
Proof.
  reflexivity. (* Equivalent to `apply eq_refl.` *)
Qed.

Definition eq_symmetric_1 A (x y : A) (H : x = y) : y = x :=
  match H in eq _ z return eq z x with
  | eq_refl _ => eq_refl x
  end.

Theorem eq_symmetric_2 : forall A (x y : A), x = y -> y = x.
Proof.
  intros.
  rewrite H. (* Replace `x` with `y` in the goal. *)
  reflexivity.
Qed.

Theorem eq_symmetric_3 : forall A (x y : A), x = y -> y = x.
Proof.
  intros.
  rewrite <- H. (* Replace `y` with `x` in the goal. *)
  reflexivity.
Qed.

Theorem eq_symmetric_4 : forall A (x y : A), x = y -> y = x.
Proof.
  intros.
  symmetry. (* Turn `y = x` into `x = y` in the goal. *)
  apply H.
Qed.

Theorem eq_symmetric_5 : forall A (x y : A), x = y -> y = x.
Proof.
  intros.
  symmetry in H. (* Turn `x = y` into `y = x` in hypothesis `H`. *)
  apply H.
Qed.

Definition eq_transitive_1 A (x y z : A) (H1 : x = y) (H2 : y = z): x = z :=
  match H2 in eq _ v return eq x v with
  | eq_refl _ =>
    match H1 in eq _ u return eq x u with
    | eq_refl _ => eq_refl x
    end
  end.

Theorem eq_transitive_2 : forall A (x y z : A), x = y -> y = z -> x = z.
Proof.
  intros.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Theorem eq_transitive_3 : forall A (x y z : A), x = y -> y = z -> x = z.
Proof.
  intros.
  rewrite <- H0.
  rewrite <- H.
  reflexivity.
Qed.

Theorem eq_transitive_4 : forall A (x y z : A), x = y -> y = z -> x = z.
Proof.
  intros.
  rewrite H0 in H. (* Replace `y` with `z` in hypothesis `H`. *)
  apply H.
Qed.

Theorem eq_transitive_5 : forall A (x y z : A), x = y -> y = z -> x = z.
Proof.
  intros.
  rewrite <- H in H0. (* Replace `y` with `x` in hypothesis `H0`. *)
  apply H0.
Qed.

(*
  *Universal quantification* corresponds to the built-in `forall` syntax. Thus,
  we don't need to define it explicitly.
*)

Definition negb_involution_1 b :=
  match b return negb (negb b) = b with
  | true => eq_refl true
  | false => eq_refl false
  end.

Check negb_involution_1. (* `forall b : bool, negb (negb b) = b` *)

Theorem negb_involution_2 : forall b, negb (negb b) = b.
Proof.
  intros.
  destruct b; reflexivity.
Qed.

(* *Existential quantification* can be defined as follows: *)

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
  ex_intro : forall x : A, P x -> ex P.

Arguments ex_intro {_} {_} _ _.

(*
  The notation for existentials is somewhat tricky to specify. If you're
  curious about the details, consult the Coq reference manual.
*)

Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, right associativity) : type_scope.

Theorem half_of_6_exists : exists x, 2 * x = 6.
Proof.
  exists 3. (* Equivalent to `apply ex_intro with (x := 3).` *)
  reflexivity.
Qed.

(*************)
(* Exercises *)
(*************)

(*
  1. Prove `False -> True` both manually and using proof mode.
  1. Prove `forall A, A /\ ~A -> False` both manually and using proof mode.
  2. Prove `forall A B, (A /\ B) <-> (B /\ A)` both manually and using proof
     mode.
  3. Prove `forall A B, (A \/ B) <-> (B \/ A)` both manually and using proof
     mode.
  4. Prove `forall A B, (A /\ B) -> (A \/ B)` both manually and using proof
     mode.
  5. Prove `forall x, x = 3 -> x * 2 = 6` both manually and using proof mode.
  6. Prove `exists x, negb x = false` both manually and using proof mode.
*)

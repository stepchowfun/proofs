(****************************)
(****************************)
(****                    ****)
(****   Writing proofs   ****)
(****                    ****)
(****************************)
(****************************)

(*
  In this lesson, we're going to redefine some things from the standard library
  to explain their definitions. We're also going to rebind some notations to
  our definitions, so we silence the relevant warning with this:
*)

#[local] Set Warnings "-notation-overridden".

(* One of our proofs will use `Nat.mul_assoc` from this module: *)

Require Import Coq.Arith.PeanoNat.

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

Arguments conj [_ _] _ _.

(*
  The following specifies that the notation `A /\ B` will be used as shorthand
  for `and A B`. The `type_scope` notation scope indicates that this notation
  only applies in contexts where a type is expected.
*)

Notation "A /\ B" := (and A B) : type_scope.

(* You can look up a notation with `Locate`. *)

Locate "/\". (* `Notation "A /\ B" := (and A B) : type_scope` *)

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

  We use `Theorem` when we want to give a name to the proof (e.g., to use it in
  a later proof) and `Goal` if the proof doesn't need a name.
*)

Theorem true_and_true_2 : True /\ True.
Proof.
  (*
    Use `split` to prove each half of a conjunction individually. Equivalently,
    we could use `apply conj`.
  *)
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

Goal True /\ False.
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

Definition modus_ponens (A B : Prop) : (A -> B) -> A -> B :=
  fun H1 H2 => H1 H2.

Goal forall A B : Prop, (A -> B) -> A -> B.
Proof.
  intros.
  apply H.
  apply H0.
Qed.

Definition conjunction_symmetric A B : A /\ B -> B /\ A :=
  fun H1 =>
    match H1 with
    | conj H2 H3 => conj H3 H2
    end.

Goal forall A B, A /\ B -> B /\ A.
Proof.
  (* `intros` moves the premises of the goal into the context. *)
  intros.

  (*
    `destruct` does pattern matching. We can `destruct` a proof of `A /\ B` to
    get access to the proofs of `A` and `B`.
  *)
  destruct H.

  (* The rest is familiar. *)
  split.
  - apply H0.
  - apply H.
Qed.

Definition explosion (A : Prop) : False -> A :=
  fun H =>
    match H with
    (* No cases to worry about! *)
    end.

Check explosion. (* `forall A : Prop, False -> A` *)

Goal forall A : Prop, False -> A.
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

Definition A_iff_A A : A <-> A :=
  conj (fun H => H) (fun H => H).

Goal forall A, A <-> A.
Proof.
  intros.
  unfold iff. (* `unfold` replaces a name with its definition. *)
  split; intros; apply H.
Qed.

(*
  To prove the *disjunction* "A or B", we must provide either a proof of "A" or
  a proof of "B".
*)

Inductive or (A B : Prop) : Prop :=
| or_introl : A -> or A B
| or_intror : B -> or A B.

Arguments or_introl [_ _] _.
Arguments or_intror [_ _] _.

Notation "A \/ B" := (or A B) : type_scope.

Definition disjunction_symmetric A B : (A \/ B) -> (B \/ A) :=
  fun H1 =>
    match H1 with
    | or_introl H2 => or_intror H2
    | or_intror H2 => or_introl H2
    end.

Goal forall A B, (A \/ B) -> (B \/ A).
Proof.
  intros.
  destruct H. (* `destruct` does case analysis on a disjunctive hypothesis. *)
  - right. (* Equivalent to `apply or_intror.` *)
    apply H.
  - left. (* Equivalent to `apply or_introl.` *)
    apply H.
Qed.

(* In Coq, the *negation* "not A" is defined as "A implies False". *)

Definition not (A : Prop) := A -> False.

Notation "~ A" := (not A) : type_scope.

Definition not_false : ~False := fun H => H.

Goal ~False.
Proof.
  unfold not.
  intros.
  apply H.
Qed.

(*
  In Lesson 2, we learned that Coq has a built-in notion of equality which is
  used for type checking: two expressions are considered equal if they compute
  to syntactically identical expressions. This is definitional equality.

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

Inductive eq [A] (x : A) : A -> Prop :=
| eq_refl : eq x x.

Notation "x = y" := (eq x y) : type_scope.
Notation "x <> y" := (~ (x = y)) : type_scope.

Definition one_plus_one_equals_two : 1 + 1 = 2 := eq_refl 2.

Goal 1 + 1 = 2.
Proof.
  reflexivity. (* Equivalent to `apply eq_refl.` *)
Qed.

Definition eq_symmetric A (x y : A) : x = y -> y = x :=
  fun H =>
    match H in _ = z return z = x with
    | eq_refl _ => eq_refl x
    end.

Goal forall A (x y : A), x = y -> y = x.
Proof.
  intros.
  rewrite H. (* Replace `x` with `y` in the goal. *)
  reflexivity.
Qed.

Goal forall A (x y : A), x = y -> y = x.
Proof.
  intros.
  rewrite <- H. (* Replace `y` with `x` in the goal. *)
  reflexivity.
Qed.

Goal forall A (x y : A), x = y -> y = x.
Proof.
  intros.
  symmetry. (* Turn `y = x` into `x = y` in the goal. *)
  apply H.
Qed.

Goal forall A (x y : A), x = y -> y = x.
Proof.
  intros.
  symmetry in H. (* Turn `x = y` into `y = x` in hypothesis `H`. *)
  apply H.
Qed.

Definition eq_transitive A (x y z : A) : x = y -> y = z -> x = z :=
  fun H1 H2 =>
    match H2 in _ = v return x = v with
    | eq_refl _ => H1
    end.

Goal forall A (x y z : A), x = y -> y = z -> x = z.
Proof.
  intros.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Goal forall A (x y z : A), x = y -> y = z -> x = z.
Proof.
  intros.
  rewrite <- H0.
  rewrite <- H.
  reflexivity.
Qed.

Goal forall A (x y z : A), x = y -> y = z -> x = z.
Proof.
  intros.
  rewrite H0 in H. (* Replace `y` with `z` in hypothesis `H`. *)
  apply H.
Qed.

Goal forall A (x y z : A), x = y -> y = z -> x = z.
Proof.
  intros.
  rewrite <- H in H0. (* Replace `y` with `x` in hypothesis `H0`. *)
  apply H0.
Qed.

(*
  *Universal quantification* corresponds to the built-in `forall` syntax. Thus,
  we don't need to define it explicitly.
*)

Definition negb_involution b :=
  match b return negb (negb b) = b with
  | true => eq_refl true
  | false => eq_refl false
  end.

Check negb_involution. (* `forall b : bool, negb (negb b) = b` *)

Goal forall b, negb (negb b) = b.
Proof.
  intros.
  destruct b; reflexivity.
Qed.

Definition weird f :
  (forall x, f (f x) = 1 + x) ->
  forall y, f (f (f (f y))) = 2 + y
:=
  fun H1 y =>
    match H1 (1 + y) in _ = z return f (f (f (f y))) = z with
    | eq_refl _ =>
      match H1 y in _ = z return f (f (f (f y))) = f (f z) with
      | eq_refl _ => eq_refl (f (f (f (f y))))
      end
    end.

Goal
  forall f,
  (forall x, f (f x) = 1 + x) ->
  forall y, f (f (f (f y))) = 2 + y.
Proof.
  intros.
  rewrite H.
  rewrite H.
  reflexivity.
Qed.

(* *Existential quantification* can be defined as follows: *)

Inductive ex [A : Type] (P : A -> Prop) : Prop :=
  ex_intro : forall x : A, P x -> ex P.

Arguments ex_intro [_ _] _ _.

(*
  The notation for existentials is somewhat tricky to specify. If you're
  curious about the details, consult the Coq reference manual.
*)

Notation "'exists' x .. y , p" := (ex (fun x => .. (ex (fun y => p)) ..))
  (at level 200, x binder, right associativity) : type_scope.

Definition half_of_6_exists : exists x, 2 * x = 6 :=
  ex_intro 3 (eq_refl 6).

Goal exists x, 2 * x = 6.
Proof.
  exists 3. (* Equivalent to `apply ex_intro with (x := 3).` *)
  reflexivity.
Qed.

Definition divisible_by_4_implies_even x :
  (exists y, 4 * y = x) ->
  (exists z, 2 * z = x)
:=
  fun H1 =>
    match H1 with
    | ex_intro y H2 =>
      ex_intro
        (2 * y)
        match eq_sym (Nat.mul_assoc 2 2 y) in Logic.eq _ z return z = x with
        | Logic.eq_refl _ => H2
        end
    end.

Goal forall x, (exists y, 4 * y = x) -> (exists z, 2 * z = x).
Proof.
  intros.
  destruct H. (* What is `y`? *)
  exists (2 * x0).
  rewrite Nat.mul_assoc.
  apply H.
Qed.

(*************)
(* Exercises *)
(*************)

(*
  1. Prove `forall (A B C : Prop), (A -> B) -> (A -> C) -> A -> B /\ C` both
     manually and using proof mode.
  2. Prove `forall (A B : Prop), (A /\ B) -> (A \/ B)` both manually and using
     proof mode.
  3. Prove `forall A : Prop, ~(A /\ ~A)` both manually and using proof mode.
  4. Prove `forall A : Prop, ~~~A -> ~A` both manually and using proof mode.
  5. Prove `forall x, x = 0 \/ exists y, S y = x` both manually and using proof
     mode.
*)

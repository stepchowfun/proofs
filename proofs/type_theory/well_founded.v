(**************************************************)
(**************************************************)
(****                                          ****)
(****   Well-founded recursion and induction   ****)
(****                                          ****)
(**************************************************)
(**************************************************)

Require Import Stdlib.Arith.Peano_dec.
Require Import Stdlib.Arith.Wf_nat.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Program.Program.
Require Import Stdlib.extraction.Extraction.
Require Import Stdlib.micromega.Lia.
Require Import main.tactics.

Import Stdlib.Lists.List.ListNotations.

(*
  Rocq allows recursive definitions, but only if the recursion happens on
  structural subterms of the input. This restriction ensures that all functions
  terminate on every input, preventing `False` from being proven with infinite
  recursion. See [file:proofs/tutorial/lesson5_consistency.v] for more details.

  Merge sort and Euclid's algorithm are common examples of recursive functions
  that don't satisfy the restriction. We'll consider a simpler example:
*)

Fail Fixpoint alternate (l : list nat) :=
  match l with
  | [] => []
  | h :: t => h :: alternate (rev t)
  end.

(*
  ```
  The command has indeed failed with message:
  Recursive definition of alternate is ill-formed.
  ```

  Intuitively, `alternate` should always terminate since it recurses on a
  smaller (but not structurally smaller) list than the input list. Eventually,
  the recursion should bottom out on the empty list. Rocq doesn't know that
  automatically, but we can persuade it.

  The strategy is to define a function that returns a "call tree" on which we
  can do structural recursion. Interpreted logically, a call tree is a proof
  that recursion will terminate on a given input, and the function that
  computes call trees is a proof that recursion terminates on all inputs.

  We define the type of call trees to live in the `Prop` universe so that
  call trees get erased during extraction. The type has an argument
  corresponding to the input list, so from a logical perspective it's a
  predicate.
*)

Inductive CallTree : list nat -> Prop :=
| ct_empty : CallTree []
| ct_nonempty : forall h t, CallTree (rev t) -> CallTree (h :: t).

(*
  Proving that the recursion terminates on all inputs is equivalent to showing
  that the predicate holds on all lists. The proof is the function that
  constructs call trees:
*)

Theorem terminates : forall l, CallTree l.
Proof.
  assert (forall n l, length l = n -> CallTree l).
  - induction n; intros; destruct l; search.
    apply ct_nonempty.
    apply IHn.
    rewrite length_rev.
    search.
  - intros.
    apply H with (n := length l).
    search.
Defined. (* Not `Qed` so we can compute with it *)

(*
  To define `alternate`, the idea is to recurse on the call tree produced by
  `terminates l`. That satisfies the termination checker, but now we have a new
  problem:
*)

Fail Definition alternate l := (
  fix recurse l (pl : CallTree l) :=
    match pl with
    | ct_empty => []
    | ct_nonempty h t pt => h :: recurse (rev t) pt
    end
) l (terminates l).

(*
  ```
  The command has indeed failed with message:
  Incorrect elimination of "pl" in the inductive type "CallTree":
  the return type has sort "Set" while it should be SProp or Prop.
  Elimination of an inductive object of sort Prop
  is not allowed on a predicate in sort "Set"
  because proofs can be eliminated only to build proofs.
  ```

  In other type theories, we might not have this problem. But Rocq generally
  doesn't allow recursion on proofs (terms whose types are in `Prop`) to
  produce non-proofs so that proofs can be erased during extraction. See
  [file:proofs/tutorial/lesson6_extraction.v] for details.

  Despite this restriction on `Prop`, `CallTree l` lives in `Prop` for a good
  reason: so we could use facts about arithmetic to construct call trees in the
  definition of `terminates` above. We'll find a way out of this pickle in a
  moment.

  Interestingly, we can prove that `CallTree l` is a *mere proposition* in the
  sense of homotopy type theory (i.e., any two call trees for a given input
  list are equal). The proof relies on equality of `list nat` being decidable.
*)

Theorem invert_ct_empty : forall p : CallTree [], p = ct_empty.
Proof.
  intro.
  refine (
    match p
    in CallTree l
    return forall q : l = [], eq_rect _ _ p _ q = ct_empty
    with
    | ct_empty => _
    | ct_nonempty h t pt => _
    end eq_refl
  ); intros; search.
  rewrite <- (Eqdep_dec.eq_rect_eq_dec (list_eq_dec eq_nat_dec) _ _ q).
  reflexivity.
Qed.

Theorem invert_ct_nonempty :
  forall h t (pl : CallTree (h :: t)),
  exists pt : CallTree (rev t),
  pl = ct_nonempty h t pt.
Proof.
  intros.
  refine (
    match pl
    in CallTree l
    return
      forall q : l = h :: t, exists pt, eq_rect _ _ pl _ q = ct_nonempty h t pt
    with
    | ct_empty => _
    | ct_nonempty h t pt => _
    end eq_refl
  ); intros; search.
  inversion q.
  subst.
  exists pt.
  rewrite <- (Eqdep_dec.eq_rect_eq_dec (list_eq_dec eq_nat_dec) _ _ q).
  reflexivity.
Qed.

Goal forall l (p1 p2 : CallTree l), p1 = p2.
Proof.
  assert (forall n l, length l <= n -> forall (p1 p2 : CallTree l), p1 = p2).
  - induction n; intros.
    + inversion H.
      destruct l; search.
      rewrite (invert_ct_empty p1).
      rewrite (invert_ct_empty p2).
      reflexivity.
    + destruct l.
      * rewrite (invert_ct_empty p1).
        rewrite (invert_ct_empty p2).
        reflexivity.
      * destruct (invert_ct_nonempty _ _ p1).
        destruct (invert_ct_nonempty _ _ p2).
        subst.
        feed (IHn (rev l)).
        rewrite length_rev.
        search.
  - intros.
    apply H with (n := length l).
    search.
Qed.

(*
  It turns out that we can define `CallTree` in a different but equivalent way
  to convince Rocq that call trees can be safely erased during extraction:
*)

Inductive CallTree' (l : list nat) : Prop :=
| ct : (forall h t, l = h :: t -> CallTree' (rev t)) -> CallTree' l.

(*
  The requirements are:

  1. There is at most one constructor.
  2. The non-parameter arguments to that constructor (if it exists) are proofs.

  Crucially, `l` is a non-uniform parameter. If it were a regular parameter, we
  wouldn't be able to instantiate it to `rev t` for the recursive branches. But
  if it were an index, then it would have to be an argument to the constructor,
  which would violate requirement (2).

  Let's prove that the revised predicate holds on all possible inputs.
*)

Theorem terminates' : forall l, CallTree' l.
Proof.
  assert (forall n l, length l = n -> CallTree' l).
  - induction n; intros; destruct l.
    + search.
    + search.
    + search.
    + apply ct.
      intros.
      apply IHn.
      rewrite length_rev.
      inversion H0.
      search.
  - intros.
    apply H with (n := length l).
    reflexivity.
Defined. (* Not `Qed` so we can compute with it *)

(* Now we can define `alternate` with some help from the *convoy pattern*. *)

Definition alternate (l : list nat) :=
  CallTree'_rect
    (fun _ => list nat)
    (
      fun l _ =>
        match l return (forall h t, l = h :: t -> _) -> _ with
        | [] => fun _ => []
        | h :: t => fun recurse => h :: recurse h t eq_refl
        end
    )
    l
    (terminates' l).

Compute alternate [1; 2; 3; 4; 5]. (* `[1; 5; 2; 4; 3]` *)

(* Let's prove something about the function. *)

Goal forall l, length (alternate l) = length l.
Proof.
  intros.
  unfold alternate.
  set (term := terminates' l).
  outro term.
  induction l using (fun P f l => CallTree'_ind P f l (terminates' l)).
  intros.
  destruct term.
  cbn.
  destruct l; search.
  cbn.
  rewrite (H0 n l eq_refl (c n l eq_refl)).
  rewrite length_rev.
  search.
Qed.

(*
  When we extract this function, the resulting code is straightforward enough,
  although some vestigial structure from the convoy pattern is visible:
*)

Extraction alternate.

(*
  ```
  (** val alternate : nat list -> nat list **)

  let rec alternate l =
    let x = fun _ t -> alternate (rev t) in
  (match l with
  | Nil -> Nil
  | Cons (h, t) -> Cons (h, (x h t)))
  ```

  Rocq's standard library has a generalization of `CallTree'` called `Acc`,
  which is short for "accessible".
*)

Print Acc.

(*
  ```
  Inductive Acc (A : Type) (R : A -> A -> Prop) (x : A) : Prop :=
    Acc_intro : (forall y : A, R y x -> Acc R y) -> Acc R x.
  ```

  To use it, we need to choose a relation `R` that determines the subtrees. We
  could choose `R` to match the way we defined `CallTree'` above:
*)

Definition R (l1 l2 : list nat) := exists x, x :: rev l1 = l2.

(*
  But let's do something different. The following relation, which compares the
  lengths of the given lists, more closely reflects the intuition for why
  `alternate` should terminate: it only recurses on lists that are smaller than
  the input lists.
*)

Definition compare_lengths (l1 l2 : list nat) := length l1 < length l2.

(*
  Analogous to what we did above, proving termination is equivalent to showing
  that every list is accessible. If we can do that, then the `compare_lengths`
  relation is said to be *well-founded*.
*)

Print well_founded.

(*
  ```
  well_founded
    = fun (A : Type) (R : A -> A -> Prop) => forall a : A, Acc R a
    : forall [A : Type], (A -> A -> Prop) -> Prop
  ```
*)

Goal well_founded compare_lengths.
Proof.
  assert (forall n l, length l <= n -> Acc compare_lengths l).
  - induction n; intros; apply Acc_intro; unfold compare_lengths; intros.
    + lia.
    + apply IHn.
      lia.
  - intro.
    apply H with (n := length a).
    lia.
Qed.

(*
  The `compare_lengths` relation is based on a *measure*: the length of the
  list. It turns out that the well-foundedness of measure-based relations is
  automatic as long as the underlying relation (in this case `<` on natural
  numbers) is itself well-founded. So we can write the proof like this instead:
*)

Theorem compare_lengths_well_founded : well_founded compare_lengths.
Proof.
  exact (measure_wf lt_wf _).
Defined. (* Not `Qed` so we can compute with it *)

(*
  To define the `alternate` function in terms of the accessibility predicate,
  we'll recurse on the proof that the input list is accessible, i.e., the call
  tree. We can use the recursor for `Acc`:
*)

Check Acc_rect.

(*
  ```
  Acc_rect :
    forall (A : Type) (R : A -> A -> Prop) (P : A -> Type),
    (
      forall x : A,
      (forall y : A, R y x -> Acc R y) ->
      (forall y : A, R y x -> P y) ->
      P x
    ) ->
    forall x : A, Acc R x -> P x
  ```

  Now let's define our recursive function.
*)

#[program] Definition alternate' (l : list nat) :=
  Acc_rect
    (fun _ => list nat)
    (fun l _ =>
      match l return (forall l' : _, compare_lengths l' l -> _) -> _ with
      | [] => fun _ => []
      | h :: t => fun recurse => h :: recurse (rev t) _
      end
    )
    (compare_lengths_well_founded l).
Final Obligation.
  intros.
  unfold compare_lengths.
  rewrite length_rev.
  auto.
Qed.

Compute alternate' [1; 2; 3; 4; 5]. (* `[1; 5; 2; 4; 3]` *)

(* Let's do the length preservation proof for this version. *)

Goal forall l, length (alternate' l) = length l.
Proof.
  intros.
  unfold alternate'.
  set (acc := compare_lengths_well_founded l).
  outro acc.
  induction l using (well_founded_induction compare_lengths_well_founded).
  intros.
  destruct acc.
  cbn.
  destruct l; search.
  cbn.
  specialize (H (rev l)).
  feed H.
  - unfold compare_lengths.
    rewrite length_rev.
    search.
  - rewrite (H (a (rev l) (alternate'_obligation_1 n l))).
    rewrite length_rev.
    search.
Qed.

(* The extracted code is even better than before: *)

Extraction alternate'.

(*
  ```
  (** val alternate' : nat list -> nat list **)

  let rec alternate' = function
  | Nil -> Nil
  | Cons (h, t) -> Cons (h, (alternate' (rev t)))
  ```

  The standard library has a function called `Fix` which is slightly more
  convenient to use than `Acc_rect`:
*)

Check Fix.

(*
  ```
  Fix :
    forall (A : Type) (R : A -> A -> Prop),
    well_founded R ->
    forall P : A -> Type,
    (forall x : A, (forall y : A, R y x -> P y) -> P x) ->
    forall x : A, P x
  ```

  We can use `Fix` to define the recursive function with slightly less code
  than before:
*)

#[program] Definition alternate'' : list nat -> list nat :=
  Fix compare_lengths_well_founded
    (fun _ => list nat)
    (fun l =>
      match l return (forall l' : _, compare_lengths l' l -> _) -> _ with
      | [] => fun _ => []
      | h :: t => fun recurse => h :: recurse (rev t) _
      end
    ).
Final Obligation.
  intros.
  unfold compare_lengths.
  rewrite length_rev.
  auto.
Qed.

Compute alternate'' [1; 2; 3; 4; 5]. (* `[1; 5; 2; 4; 3]` *)

(* The length preservation proof is similar to the previous one. *)

Goal forall l, length (alternate'' l) = length l.
Proof.
  intros.
  unfold alternate''.
  unfold Fix.
  set (acc := compare_lengths_well_founded l).
  outro acc.
  induction l using (well_founded_induction compare_lengths_well_founded).
  intros.
  destruct acc.
  cbn.
  destruct l; search.
  cbn.
  specialize (H (rev l)).
  feed H.
  - unfold compare_lengths.
    rewrite length_rev.
    search.
  - rewrite (H (a (rev l) (alternate''_obligation_1 n l))).
    rewrite length_rev.
    search.
Qed.

(* Extraction produces the same code as before: *)

Extraction alternate''.

(*
  ```
  (** val alternate'' : nat list -> nat list **)

  let rec alternate'' = function
  | Nil -> Nil
  | Cons (h, t) -> Cons (h, (alternate'' (rev t)))
  ```

  The `#[program] Fixpoint` command allows us to define the function even more
  simply:
*)

#[program] Fixpoint alternate''' (l : list nat) {measure (length l)} :=
  match l with
  | [] => []
  | h :: t => h :: alternate''' (rev t)
  end.
Final Obligation.
  intros.
  rewrite length_rev.
  search.
Qed.

Compute alternate''' [1; 2; 3; 4; 5]. (* `[1; 5; 2; 4; 3]` *)

(*
  Note the use of `measure` in the definition. With that, Rocq was able to
  prove the well-foundedness of the relation automatically without using the
  `compare_lengths_well_founded` proof from above.

  Unfortunately, it's difficult to prove properties about functions defined via
  `#[program] Fixpoint`, since the generated code can be quite complicated.
*)

Print alternate'''. (* Long output *)

(* Extraction produces code that relies on a mysterious `fix_sub` function: *)

Extraction alternate'''.

(*
  ```
  (** val alternate''' : nat list -> nat list **)

  let alternate''' =
    fix_sub (fun recarg alternate'''' ->
  match recarg with
  | Nil -> Nil
  | Cons (h, t) -> Cons (h, (alternate'''' (rev t))))
  ```

  Of the various approaches we've seen, I think `alternate''` is the best one
  for most purposes. It's simple to write and reason about, and it produces
  good extracted code.
*)

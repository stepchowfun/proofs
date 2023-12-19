(**************************************)
(**************************************)
(****                              ****)
(****   Extracting verified code   ****)
(****                              ****)
(**************************************)
(**************************************)

(*************************************************)
(* Information cannot leave the `Prop` universe. *)
(*************************************************)

(*
  Everything in `Prop` is considered a proposition, and the inhabitants of
  those propositions are considered proofs. For example, the following
  proposition has two proofs:
*)

Inductive myProp : Prop :=
| proof1 : myProp
| proof2 : myProp.

(* Since `myProp` is an inductive type, it supports pattern matching. *)

Definition flipFlop (proof : myProp) : myProp :=
  match proof with
  | proof1 => proof2
  | proof2 => proof1
  end.

(*
  As we will see in this lesson, Coq code can be "extracted" into code in other
  languages such that the proofs are erased. But in order for extraction to
  make sense, it's important that none of the extracted code makes decisions
  based on the erased proofs. Coq guarantees this with a restriction on pattern
  matching. The following is rejected because the return type is not in `Prop`:
*)

Fail Definition myPropToNat (proof : myProp) : nat :=
  match proof with
  | proof1 => 0
  | proof2 => 1
  end.

(*
  ```
  The command has indeed failed with message:
  Incorrect elimination of "proof" in the inductive type "myProp":
  the return type has sort "Set" while it should be "SProp" or "Prop".
  Elimination of an inductive object of sort Prop
  is not allowed on a predicate in sort Set
  because proofs can be eliminated only to build proofs.
  ```

  However, if a proposition has zero constructors or one constructor for which
  the non-parameter arguments are proofs, then pattern matching on it doesn't
  result in any decisions being made based on the proof. Thus, Coq allows the
  following:
*)

Definition falseToNat (proof : False) : nat :=
  match proof with
  end.

Definition trueToNat (proof : True) : nat :=
  match proof with
  | I => 0
  end.

Definition falseAndTrueToNat (proof : False /\ True) : nat :=
  match proof with
  | conj _ _ => 0
  end.

Definition eqToNat (proof : false = false) : nat :=
  match proof with
  | eq_refl _ => 0
  end.

(*************************************)
(* Extracting verified code to OCaml *)
(*************************************)

(* This allows us to use Boolean operators such as `&&` and `||`. *)

#[local] Open Scope bool_scope.

(* Let's define an xor function and prove it correct. *)

Definition xor b1 b2 :=
  match (b1, b2) with
  | (true, true) => false
  | (false, false) => false
  | (true, false) => true
  | (false, true) => true
  end.

Goal forall b1 b2, xor b1 b2 = (b1 || b2) && negb (b1 && b2).
Proof.
  intros.
  destruct b1; destruct b2; reflexivity.
Qed.

(* Now let's extract the code to OCaml. *)

Require Coq.extraction.Extraction.

Recursive Extraction xor.

(*
  ```
  type bool =
  | True
  | False

  (** val xor : bool -> bool -> bool **)

  let xor b1 b2 =
    match b1 with
    | True -> (match b2 with
               | True -> False
               | False -> True)
    | False -> b2
  ```

  This code works, but it would be better if the arguments of `xor` were OCaml
  `bool`s rather than using an extracted copy of `bool`. To address this, we
  can teach Coq about OCaml `bool`s.
*)

Extract Inductive bool => "bool" ["true" "false"].

Recursive Extraction xor.

(*
  ```
  (** val xor : bool -> bool -> bool **)

  let xor b1 b2 =
    if b1 then if b2 then false else true else b2
  ```

  We've formally verified a function and extracted it to OCaml! In practice,
  we'd extract the code to a file to be fed to the OCaml compiler:

  ```
  Extraction "xor.ml" xor.
  ```

  Instead of writing code and separately proving theorems about it, we can
  write code which manipulates proofs.

  First, let's teach Coq about OCaml integers. Note that this is not completely
  correct, because OCaml integers are bounded while Coq's `nat` has no upper
  bound. We proceed anyway since we want to keep the example simple.
*)

Extract Inductive nat => "int"
  ["0" "(fun x -> x + 1)"]
  "(fun zero succ n -> if n = 0 then zero () else succ (n - 1))".

Extract Constant plus => "( + )".

(*
  The Coq standard library defines the following:

  ```
  Inductive sig (A : Type) (P : A -> Prop) : Type :=
  | exist : forall x : A, P x -> sig P.

  Notation "{ x | P }" := (sig (fun x => P)) : type_scope.
  ```

  This can be used to define *subset types*, such as the type of even `nat`s:
*)

Definition evenNat := { n : nat | exists m, n = 2 * m }.

(* We can define addition on `evenNat`s using proof mode. *)

Require Import Coq.micromega.Lia.

Definition addEvenNat1 : forall (n m : evenNat), evenNat.
Proof.
  unfold evenNat.
  refine (fun n m => _). (* Define a function and postpone the body. *)
  destruct n. (* Unpack `n` into a `nat` and a proof of its evenness. *)
  destruct m. (* Do the same for `m`. *)
  refine (exist _ (x + x0) _). (* Add the `nat`s and postpone the proof. *)
  destruct e.
  destruct e0.
  exists (x1 + x2).
  lia.
Defined. (* Unlike `Qed`, `Defined` grants us access to the implementation. *)

Recursive Extraction addEvenNat1.

(*
  The extracted code omits the proofs:

  ```
  type 'a sig0 = 'a
    (* singleton inductive, whose constructor was exist *)

  (** val add : int -> int -> int **)

  let rec add = ( + )

  type evenNat = int

  (** val addEvenNat1 : evenNat -> evenNat -> evenNat **)

  let addEvenNat1 =
    add
  ```

  Coq provides a more convenient way to write this style of code:
*)

Program Definition addEvenNat2 (n m : evenNat) : evenNat := n + m.
Next Obligation.
  destruct n.
  destruct m.
  destruct e.
  destruct e0.
  exists (x1 + x2).
  cbn. (* Simplify the goal. *)
  lia.
Defined.

Recursive Extraction addEvenNat2.

(*
  The extracted code is essentially the same as before:

  ```
  type 'a sig0 = 'a
    (* singleton inductive, whose constructor was exist *)

  (** val add : int -> int -> int **)

  let rec add = ( + )

  type evenNat = int

  (** val addEvenNat2 : evenNat -> evenNat -> evenNat **)

  let addEvenNat2 =
    add
  ```
*)

(*************)
(* Exercises *)
(*************)

(*
  1. Explain why Coq doesn't generally let us pattern match on a proof to
     produce something which is not a proof. What are the exceptions to this
     rule?
  2. Write a function of type `nat -> nat` which takes a `nat` and doubles it,
     prove some property about it, and extract it to OCaml.
  3. Write a function which takes a `nat` and doubles it, but give the function
     a type that guarantees the property from the previous question. Extract it
     to OCaml.
  4. We've seen two styles of writing formally verified code: (1) write the
     code in an ordinary functional style and prove properties about it
     separately (as we did with `xor`), and (2) write the code and proofs
     together (as we did with `addEvenNat1` and `addEvenNat2`). When might you
     use one style over the other?
*)

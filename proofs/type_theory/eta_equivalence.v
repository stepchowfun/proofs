(*****************************)
(*****************************)
(****                     ****)
(****   Eta equivalence   ****)
(****                     ****)
(*****************************)
(*****************************)

(*
  Coq does not eta-contract terms during reduction. Suppose we had the
  following function:
*)

Parameter f : nat -> unit.

(* Consider the eta expansion of that function: *)

Check fun x => f x.

(*
  If we have eta contraction for function types and eta expansion for the unit
  type (which is the only reasonable direction for the unit type), then the
  above term has two normal forms:
*)

Check f. (* Eta-contract the function *)
Check fun x => tt. (* Eta-expand the body of the function *)

(*
  So, we can't have both forms of eta if we care about confluence.

  Eta contraction can also break subject reduction when combined with universe
  cumulativity. Consider the type of the following function:
*)

Universes U0 U1.
Constraint U0 < U1.

Check fun (x : Type@{U0}) => (fun (y : Type@{U1}) => y) x.

(*
  The type is `Type@{U0} -> Type@{U1}` (you may need to configure your Coq
  environment to display universe levels in order to see this). Now consider
  the type of its eta-contracted form:
*)

Check (fun (y : Type@{U1}) => y).

(*
  Now the type is `Type@{U1} -> Type@{U1}`. In Coq, neither of those two types
  is convertible to the other, since Coq does not have contravariance.

  What about eta expansion? The problem is that eta expansion is non-
  normalizing.

  An infinite eta expansion:
*)

Check f.
Check fun x => f x.
Check fun y => (fun x => f x) y.
Check fun z => (fun y => (fun x => f x) y) z.

(* A cycle: *)

Check f 0.
Check (fun x => f x) 0.
Check f 0.

(* Another cycle: *)

Check fun (x : nat) => x.
Check fun (y : nat) => (fun x => x) y.
Check fun (y : nat) => y.

(*
  To prevent this, we can disallow eta expansion on lambdas and applicands
  (terms being applied to arguments).

  So this expansion is fine:
*)

Check f.
Check fun x => f x.

(* But these expansions are not: *)

Check f 0.
Check (fun x => f x) 0.

Check fun (x : nat) => x.
Check fun (y : nat) => (fun x => x) y.

(*
  For products, we have an analagous issue with non-normalization, and we can
  restrict eta expansion in a similar way to fix it.

  But unfortunately, with these restrictions on eta expansion, evaluation is no
  longer a rewriting system, since whether eta expansion is valid would depend
  on the evaluation context. For more on this topic, see [2].

  Coq implements eta conversion for functions, but does not do eta expansion or
  contraction during reduction. Thus, we have the following in Coq:
*)

Goal
  forall (A : Type) (B : A -> Type) (f : forall (x : A), B x),
  f = fun x => f x.
Proof.
  reflexivity.
Qed.

(*
  However, Coq doesn't have eta conversion for (co)inductive types.

  Eta conversion for identity types implies that propositional equality is
  equivalent to judgmental equality, rendering type checking undecidable [3].
  Eta conversion for recursive types also makes type checking undecidable [4].
  So eta conversion is incompatible with indices and recursive types.

  Types declared with `Record` support neither indices nor recursion, so eta
  conversion (but not expansion or contraction) is supported for them.
*)

Record Square := { width : nat; height : nat; square : width = height }.

Goal
  forall s,
  s = {| width := s.(width); height := s.(height) ; square := s.(square) |}.
Proof.
  reflexivity.
Qed.

(*
  Even though eta-conversion for (co)inductive types is generally absent,
  corresponding eta laws can be proven in many cases.
*)

Goal forall x : unit, x = tt.
Proof.
  destruct x.
  reflexivity.
Qed.

(*
  References:

  [1] https://www.meven.ac/documents/22-WITS-abstract.pdf
  [2] Jay, C. Barry, and Neil Ghani. "The Virtues of Eta-Expansion." Journal of
      Functional Programming 5, no. 2 (1995): 135–54.
      https://doi.org/10.1017/S0956796800001301.
  [3] https://ncatlab.org/nlab/show/identity+type#EtaConversion
  [4] https://proofassistants.stackexchange.com/a/1503
*)

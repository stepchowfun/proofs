(**********************************************)
(**********************************************)
(****                                      ****)
(****   Programming with dependent types   ****)
(****                                      ****)
(**********************************************)
(**********************************************)

Require Import String.

(* A length-indexed list of strings *)

Inductive slist : nat -> Type :=
| snil : slist O
| scons :
    forall {n}, (* Length of the tail, implicit due to the curly braces *)
    string ->   (* Head *)
    slist n ->  (* Tail *)
    slist (S n).

(* Let's construct some slists. *)

Check snil. (* slist 0 *)
Check scons "foo" snil. (* slist 1 *)
Check scons "hello" (scons "world" snil). (* slist 2 *)

(*
  Here's a function which produces an slist of a given length containing empty
  strings.
*)

Fixpoint empty_strings n1 : slist n1 :=
  match n1 with
  | O => snil
  | S n2 => scons "" (empty_strings n2)
  end.

(*
  Here's a function which concatenates two slists. This demonstrates how to do
  dependent pattern matching.
*)

Fixpoint concat {n1 n2}
         (l1 : slist n1)
         (l2 : slist n2) :
         slist (n1 + n2) :=
  match l1 in slist n3
  return slist (n3 + n2) (* Here, n3 = n1. *)
  with
  | snil => l2 (* But n3 = 0 here. *)
  | scons x l3 => scons x (concat l3 l2) (* And n3 = S (len l3) here. *)
  end.

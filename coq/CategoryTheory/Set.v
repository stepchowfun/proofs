(*************************************************************)
(*************************************************************)
(****                                                     ****)
(****   A proof that sets and functions form a category   ****)
(****                                                     ****)
(*************************************************************)
(*************************************************************)

Require Import Main.CategoryTheory.Category.
Require Import Main.Tactics.

Definition setCategory : category.
Proof.
  refine (
    newCategory
    Set
    (fun x y => x -> y)
    (fun x y z f g e => f (g e))
    (fun x e => e)
    _ _
  ); magic.
Defined.

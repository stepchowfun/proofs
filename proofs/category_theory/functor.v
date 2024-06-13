(**********************)
(**********************)
(****              ****)
(****   Functors   ****)
(****              ****)
(**********************)
(**********************)

Require Import Coq.Logic.ProofIrrelevance.
Require Import main.category_theory.category.
Require Import main.tactics.

#[local] Set Universe Polymorphism.

(* Metavariables for functors: `F`, `G`, `H` *)

Record Functor C D := {
  o_map : Object C -> Object D;
  f_map [x y] : Arrow x y -> Arrow (o_map x) (o_map y);

  f_ident x : f_map (id x) = id (o_map x);
  f_comp [x y z] (f : Arrow x y) (g : Arrow y z) :
    compose (f_map f) (f_map g) = f_map (compose f g);
}.

Arguments o_map [_ _] _.
Arguments f_map [_ _] _ [_ _] _.
Arguments f_ident [_ _] _ _.
Arguments f_comp [_ _] _ [_ _ _] _ _.

Hint Resolve f_ident : main.
Hint Rewrite @f_ident : main.
Hint Resolve f_comp : main.
Hint Rewrite @f_comp : main.

Definition endofunctor C := Functor C C.

Program Definition id_functor C : endofunctor C := {|
  o_map o := o;
  f_map _ _ f := f;
|}.

Program Definition comp_functor [C D E] (F : Functor C D) (G : Functor D E) :
  Functor C E
:= {|
  o_map o := o_map G (o_map F o);
  f_map _ _ f := f_map G (f_map F f);
|}.

Theorem comp_functor_ident_left [C D] (F : Functor C D) :
  comp_functor (id_functor C) F = F.
Proof.
  unfold comp_functor.
  destruct F.
  f_equal; apply proof_irrelevance.
Qed.

Hint Resolve comp_functor_ident_left : main.

Theorem comp_functor_ident_right [C D] (F : Functor C D) :
  comp_functor F (id_functor D) = F.
Proof.
  unfold comp_functor.
  destruct F.
  f_equal; apply proof_irrelevance.
Qed.

Hint Resolve comp_functor_ident_right : main.

Theorem comp_functor_assoc
  [B C D E]
  (F : Functor B C)
  (G : Functor C D)
  (H : Functor D E)
: comp_functor (comp_functor F G) H = comp_functor F (comp_functor G H).
Proof.
  unfold comp_functor.
  f_equal; apply proof_irrelevance.
Qed.

Hint Resolve comp_functor_assoc : main.

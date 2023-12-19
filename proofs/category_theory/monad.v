(********************)
(********************)
(****            ****)
(****   Monads   ****)
(****            ****)
(********************)
(********************)

Require Import Coq.Logic.ProofIrrelevance.
Require Import main.category_theory.functor.
Require Import main.category_theory.natural_transformation.

#[local] Set Universe Polymorphism.

(* Metavariable for monads: `M` *)

Record Monad
  [C]
  [F : endofunctor C]
  (Eta : NaturalTransformation (id_functor C) F)
  (Mu : NaturalTransformation (comp_functor F F) F)
:= {
  m_assoc :
    eta (vert_comp_natural_transformation (left_whisker F Mu) Mu) =
    eta (vert_comp_natural_transformation (right_whisker Mu F) Mu);
  m_ident1 :
    eta (vert_comp_natural_transformation (left_whisker F Eta) Mu) =
    eta (id_natural_transformation F);
  m_ident2 :
    eta (vert_comp_natural_transformation (right_whisker Eta F) Mu) =
    eta (id_natural_transformation F);
}.

Arguments m_assoc [_ _ _ _] _.
Arguments m_ident1 [_ _ _ _] _.
Arguments m_ident2 [_ _ _ _] _.

#[export] Hint Resolve m_assoc : main.
#[export] Hint Resolve m_ident1 : main.
#[export] Hint Rewrite @m_ident1 : main.
#[export] Hint Resolve m_ident2 : main.
#[export] Hint Rewrite @m_ident2 : main.

Theorem eq_monad
  [C]
  [F : endofunctor C]
  (Eta : NaturalTransformation (id_functor C) F)
  (Mu : NaturalTransformation (comp_functor F F) F)
  (M1 M2 : Monad Eta Mu)
: M1 = M2.
Proof.
  destruct M1.
  destruct M2.
  f_equal; apply proof_irrelevance.
Qed.

#[export] Hint Resolve eq_monad : main.

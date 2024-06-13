(**********************)
(**********************)
(****              ****)
(****   Products   ****)
(****              ****)
(**********************)
(**********************)

Require Import main.category_theory.arrow.
Require Import main.category_theory.category.
Require Import main.category_theory.object.
Require Import main.category_theory.terminal.
Require Import main.tactics.

#[local] Set Universe Polymorphism.

(* Metavariable for products: `xy` *)
(* Metavariables for projections: `px`, `py` *)

Definition product
  [C]
  (x y xy : Object C)
  (px : Arrow xy x)
  (py : Arrow xy y)
:=
  forall z (qx : Arrow z x) (qy : Arrow z y),
  Universal (fun f => qx = compose f px /\ qy = compose f py).

Theorem product_unique C (x y : Object C) :
  UniqueUpToIsomorphism (fun xy => exists px py, product x y xy px py).
Proof.
  clean.
  unfold UniqueUpToIsomorphism. unfold product. clean.
  pose proof (H y0 x1 x2).
  pose proof (H0 x0 x3 x4).
  pose proof (H x0 x3 x4).
  pose proof (H0 y0 x1 x2).
  clear H H0.
  unfold Universal in *. clean. clear H H3 H5 H6.
  unfold ArrowExists in *. destruct H1. destruct H. destruct H2. destruct H2.
  unfold Isomorphic. unfold Isomorphism. unfold Inverse. exists x6. exists x5.
  unfold ArrowUnique in *.
  split.
  - apply H4; search.
    split; rewrite c_assoc; search.
  - apply H0; search.
    split; rewrite c_assoc; search.
Qed.

Hint Resolve product_unique : main.

Theorem product_commutator
  [C]
  (x y xy : Object C)
  (px : Arrow xy x)
  (py : Arrow xy y)
: product x y xy px py -> product y x xy py px.
Proof.
  unfold product.
  unfold Universal.
  unfold ArrowExists.
  unfold ArrowUnique.
  clean.
  specialize (H z qy qx).
  esearch.
Qed.

(*
  We deliberately avoid adding a resolve hint for `product_commutator` because
  doing so could lead to nonterminating searches.
*)

Theorem product_commutative
  [C]
  (x y xy yx : Object C)
  (px1 : Arrow xy x)
  (py1 : Arrow xy y)
  (px2 : Arrow yx x)
  (py2 : Arrow yx y)
: product x y xy px1 py1 -> product y x yx py2 px2 -> Isomorphic xy yx.
Proof.
  clean.
  apply product_commutator in H0.
  pose proof (product_unique C x y).
  unfold UniqueUpToIsomorphism in H1.
  apply H1; esearch.
Qed.

Hint Resolve product_commutative : main.

Theorem product_associative
  [C]
  (x y z xy yz xy_z x_yz : Object C)
  (xy_to_x : Arrow xy x)
  (xy_to_y : Arrow xy y)
  (yz_to_y : Arrow yz y)
  (yz_to_z : Arrow yz z)
  (xy_z_to_xy : Arrow xy_z xy)
  (xy_z_to_z : Arrow xy_z z)
  (x_yz_to_x : Arrow x_yz x)
  (x_yz_to_yz : Arrow x_yz yz)
: product x y xy xy_to_x xy_to_y ->
  product y z yz yz_to_y yz_to_z ->
  product xy z xy_z xy_z_to_xy xy_z_to_z ->
  product x yz x_yz x_yz_to_x x_yz_to_yz ->
  Isomorphic xy_z x_yz.
Proof.
  unfold product.
  clean.

  Ltac instantiate_universal H :=
    unfold Universal in H;
    unfold ArrowExists in H;
    do 3 destruct H;
    sort.

  pose proof (H x_yz x_yz_to_x (compose x_yz_to_yz yz_to_y)).
  instantiate_universal H3.
  rename x0 into x_yz_to_xy.
  clear H4.

  pose proof (H0 xy_z (compose xy_z_to_xy xy_to_y) xy_z_to_z).
  instantiate_universal H4.
  rename x0 into xy_z_to_yz.
  clear H6.

  pose proof (H2 xy_z (compose xy_z_to_xy xy_to_x) xy_z_to_yz).
  instantiate_universal H6.
  rename x0 into xy_z_to_x_yz.
  clear H8.

  pose proof (H1 x_yz x_yz_to_xy (compose x_yz_to_yz yz_to_z)).
  instantiate_universal H8.
  rename x0 into x_yz_to_xy_z.
  clear H10.

  assert (id xy_z = compose xy_z_to_x_yz x_yz_to_xy_z).
  - assert (
      compose (
        compose (compose xy_z_to_x_yz x_yz_to_xy_z) xy_z_to_xy
      ) xy_to_y = compose xy_z_to_xy xy_to_y
    ).
    + rewrite (@c_assoc C xy_z x_yz xy_z xy).
      rewrite <- H8.
      rewrite c_assoc.
      rewrite <- H5.
      rewrite <- c_assoc.
      search.
    + assert (
        compose (
          compose (compose xy_z_to_x_yz x_yz_to_xy_z) xy_z_to_xy
        ) xy_to_x = compose xy_z_to_xy xy_to_x
      ).
      * rewrite (@c_assoc C xy_z x_yz xy_z xy).
        rewrite <- H8.
        rewrite c_assoc.
        search.
      * pose proof (
          H
          xy_z
          (
            compose (
              compose (compose xy_z_to_x_yz x_yz_to_xy_z) xy_z_to_xy
            ) xy_to_x
          )
          (
            compose (
              compose (compose xy_z_to_x_yz x_yz_to_xy_z) xy_z_to_xy
            ) xy_to_y
          )
        ).
        unfold Universal in H13.
        destruct H13.
        clear H13.
        unfold ArrowUnique in H14.
        specialize (
          H14 xy_z_to_xy (
            compose (compose xy_z_to_x_yz x_yz_to_xy_z) xy_z_to_xy
          )
        ).
        do 2 feed H14.

        assert (
          compose (compose xy_z_to_x_yz x_yz_to_xy_z) xy_z_to_z = xy_z_to_z
        ); [rewrite c_assoc; rewrite <- H11; search | idtac].

        pose proof (H1 xy_z xy_z_to_xy xy_z_to_z).
        unfold Universal in H15.
        search.
  - assert (id x_yz = compose x_yz_to_xy_z xy_z_to_x_yz).
    + assert (
        compose (
          compose (compose x_yz_to_xy_z xy_z_to_x_yz) x_yz_to_yz
        ) yz_to_y = compose x_yz_to_yz yz_to_y
      ).
      * rewrite (c_assoc x_yz_to_xy_z).
        rewrite <- H9.
        rewrite c_assoc.
        rewrite <- H4.
        rewrite <- c_assoc.
        search.
      * assert (
          compose (
            compose (compose x_yz_to_xy_z xy_z_to_x_yz) x_yz_to_yz
          ) yz_to_z = compose x_yz_to_yz yz_to_z
        ).
        -- rewrite (c_assoc x_yz_to_xy_z).
           rewrite <- H9.
           rewrite c_assoc.
           search.
        -- pose proof (
             H0
             x_yz
             (
               compose (
                 compose (compose x_yz_to_xy_z xy_z_to_x_yz) x_yz_to_yz
               ) yz_to_y
             )
             (
               compose (
                 compose (compose x_yz_to_xy_z xy_z_to_x_yz) x_yz_to_yz
               ) yz_to_z
             )
           ).
           unfold Universal in H14.
           destruct H14.
           clear H14.
           unfold ArrowUnique in H15.
           specialize (
             H15 x_yz_to_yz (
               compose (compose x_yz_to_xy_z xy_z_to_x_yz) x_yz_to_yz
             )
           ).
           do 2 feed H15.

           assert (
             compose (compose x_yz_to_xy_z xy_z_to_x_yz) x_yz_to_x =
               x_yz_to_x
           ); [rewrite c_assoc; rewrite <- H6; search | idtac].

           pose proof (H2 x_yz x_yz_to_x x_yz_to_yz).
           unfold Universal in H16.
           search.
    + unfold Isomorphic.
      exists xy_z_to_x_yz.
      unfold Isomorphism.
      exists x_yz_to_xy_z.
      unfold Inverse.
      search.
Qed.

Hint Resolve product_associative : main.

Theorem product_terminal
  [C]
  (x y xy : Object C)
  (xy_to_x : Arrow xy x)
  (xy_to_y : Arrow xy y)
: product x y xy xy_to_x xy_to_y -> terminal x -> Isomorphic xy y.
Proof.
  unfold terminal.
  clean.
  pose proof (H0 y).
  clean.
  assert (product x y y x0 (id y)).
  - clear H1.
    unfold product.
    clean.
    unfold Universal.
    split.
    + unfold ArrowExists.
      exists qy.
      split; search.
      specialize (H0 z).
      search.
    + unfold ArrowUnique.
      search.
  - pose proof (product_unique C x y).
    unfold UniqueUpToIsomorphism in H3.
    specialize (H3 xy y).
    esearch.
Qed.

Hint Resolve product_terminal : main.

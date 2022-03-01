(**********************)
(**********************)
(****              ****)
(****   Products   ****)
(****              ****)
(**********************)
(**********************)

Require Import Main.CategoryTheory.Arrow.
Require Import Main.CategoryTheory.Category.
Require Import Main.CategoryTheory.Object.
Require Import Main.CategoryTheory.Terminal.
Require Import Main.Tactics.

Set Universe Polymorphism.

(* Metavariable for products: xy *)
(* Metavariables for projections: px, py *)

Definition product
  {C}
  (x y xy : object C)
  (px : arrow xy x)
  (py : arrow xy y)
:=
  forall z (qx : arrow z x) (qy : arrow z y),
  universal (fun f => qx = compose px f /\ qy = compose py f).

Theorem productUnique C (x y : object C) :
  uniqueUpToIsomorphism (fun xy => exists px py, product x y xy px py).
Proof.
  clean.
  unfold uniqueUpToIsomorphism. unfold product. clean.
  fact (H y0 x1 x2). fact (H0 x0 x3 x4). fact (H x0 x3 x4). fact (H0 y0 x1 x2).
  clear H H0.
  unfold universal in *. clean. clear H H3 H5 H6.
  unfold arrowExists in *. destruct H1. destruct H. destruct H2. destruct H2.
  unfold isomorphic. unfold isomorphism. unfold inverse. exists x6. exists x5.
  unfold arrowUnique in *.
  split.
  - apply H0; magic.
    split; rewrite cAssoc; magic.
  - apply H4; magic.
    split; rewrite cAssoc; magic.
Qed.

#[export] Hint Resolve productUnique : main.

Theorem productCommutator
  {C}
  (x y xy : object C)
  (px : arrow xy x)
  (py : arrow xy y)
: product x y xy px py -> product y x xy py px.
Proof.
  unfold product.
  unfold universal.
  unfold arrowExists.
  unfold arrowUnique.
  clean.
  specialize (H z qy qx).
  eMagic.
Qed.

(*
  We deliberately avoid adding a resolve hint for productCommutator because
  doing so could lead to nonterminating searches.
*)

Theorem productCommutative
  {C}
  (x y xy yx : object C)
  (px1 : arrow xy x)
  (py1 : arrow xy y)
  (px2 : arrow yx x)
  (py2 : arrow yx y)
: product x y xy px1 py1 -> product y x yx py2 px2 -> isomorphic xy yx.
Proof.
  clean.
  apply productCommutator in H0.
  fact (productUnique C x y).
  unfold uniqueUpToIsomorphism in H1.
  apply H1; eMagic.
Qed.

#[export] Hint Resolve productCommutative : main.

Theorem productAssociative
  {C}
  (x y z xy yz xy_z x_yz : object C)
  (xy_to_x : arrow xy x)
  (xy_to_y : arrow xy y)
  (yz_to_y : arrow yz y)
  (yz_to_z : arrow yz z)
  (xy_z_to_xy : arrow xy_z xy)
  (xy_z_to_z : arrow xy_z z)
  (x_yz_to_x : arrow x_yz x)
  (x_yz_to_yz : arrow x_yz yz)
: product x y xy xy_to_x xy_to_y ->
  product y z yz yz_to_y yz_to_z ->
  product xy z xy_z xy_z_to_xy xy_z_to_z ->
  product x yz x_yz x_yz_to_x x_yz_to_yz ->
  isomorphic xy_z x_yz.
Proof.
  unfold product.
  clean.

  Ltac instantiateUniversal H :=
    unfold universal in H;
    unfold arrowExists in H;
    do 3 destruct H;
    sort.

  fact (H x_yz x_yz_to_x (compose yz_to_y x_yz_to_yz)).
  instantiateUniversal H3.
  rename x0 into x_yz_to_xy.
  clear H4.

  fact (H0 xy_z (compose xy_to_y xy_z_to_xy) xy_z_to_z).
  instantiateUniversal H4.
  rename x0 into xy_z_to_yz.
  clear H6.

  fact (H2 xy_z (compose xy_to_x xy_z_to_xy) xy_z_to_yz).
  instantiateUniversal H6.
  rename x0 into xy_z_to_x_yz.
  clear H8.

  fact (H1 x_yz x_yz_to_xy (compose yz_to_z x_yz_to_yz)).
  instantiateUniversal H8.
  rename x0 into x_yz_to_xy_z.
  clear H10.

  assert (id = compose x_yz_to_xy_z xy_z_to_x_yz).
  - assert (
      compose xy_to_y (
        compose xy_z_to_xy (compose x_yz_to_xy_z xy_z_to_x_yz)
      ) = compose xy_to_y xy_z_to_xy
    ).
    + rewrite (@cAssoc C xy_z x_yz xy_z xy).
      rewrite <- H8.
      rewrite cAssoc.
      rewrite <- H5.
      rewrite <- cAssoc.
      magic.
    + assert (
        compose xy_to_x (
          compose xy_z_to_xy (compose x_yz_to_xy_z xy_z_to_x_yz)
        ) = compose xy_to_x xy_z_to_xy
      ).
      * rewrite (@cAssoc C xy_z x_yz xy_z xy).
        rewrite <- H8.
        rewrite cAssoc.
        magic.
      * {
        fact (
          H
          xy_z
          (
            compose xy_to_x (
              compose xy_z_to_xy (compose x_yz_to_xy_z xy_z_to_x_yz)
            )
          )
          (
            compose xy_to_y (
              compose xy_z_to_xy (compose x_yz_to_xy_z xy_z_to_x_yz)
            )
          )
        ).
        unfold universal in H13.
        destruct H13.
        clear H13.
        unfold arrowUnique in H14.
        specialize (
          H14 xy_z_to_xy (
            compose xy_z_to_xy (compose x_yz_to_xy_z xy_z_to_x_yz)
          )
        ).
        do 2 feed H14.

        assert (
          compose xy_z_to_z (compose x_yz_to_xy_z xy_z_to_x_yz) = xy_z_to_z
        ); [rewrite cAssoc; rewrite <- H11; magic | idtac].

        fact (H1 xy_z xy_z_to_xy xy_z_to_z).
        unfold universal in H15.
        magic.
      }
  - assert (id = compose xy_z_to_x_yz x_yz_to_xy_z).
    + assert (
        compose yz_to_y (
          compose x_yz_to_yz (compose xy_z_to_x_yz x_yz_to_xy_z)
        ) = compose yz_to_y x_yz_to_yz
      ).
      * rewrite (cAssoc x_yz_to_xy_z).
        rewrite <- H9.
        rewrite cAssoc.
        rewrite <- H4.
        rewrite <- cAssoc.
        magic.
      * {
        assert (
          compose yz_to_z (
            compose x_yz_to_yz (compose xy_z_to_x_yz x_yz_to_xy_z)
          ) = compose yz_to_z x_yz_to_yz
        ).
        - rewrite (cAssoc x_yz_to_xy_z).
          rewrite <- H9.
          rewrite cAssoc.
          magic.
        - fact (
            H0
            x_yz
            (
              compose yz_to_y (
                compose x_yz_to_yz (compose xy_z_to_x_yz x_yz_to_xy_z)
              )
            )
            (
              compose yz_to_z (
                compose x_yz_to_yz (compose xy_z_to_x_yz x_yz_to_xy_z)
              )
            )
          ).
          unfold universal in H14.
          destruct H14.
          clear H14.
          unfold arrowUnique in H15.
          specialize (
            H15 x_yz_to_yz (
              compose x_yz_to_yz (compose xy_z_to_x_yz x_yz_to_xy_z)
            )
          ).
          do 2 feed H15.

          assert (
            compose x_yz_to_x (compose xy_z_to_x_yz x_yz_to_xy_z) =
              x_yz_to_x
          ); [rewrite cAssoc; rewrite <- H6; magic | idtac].

          fact (H2 x_yz x_yz_to_x x_yz_to_yz).
          unfold universal in H16.
          magic.
      }
    + unfold isomorphic.
      exists xy_z_to_x_yz.
      unfold isomorphism.
      exists x_yz_to_xy_z.
      unfold inverse.
      magic.
Qed.

#[export] Hint Resolve productAssociative : main.

Theorem productTerminal
  {C}
  (x y xy : object C)
  (xy_to_x : arrow xy x)
  (xy_to_y : arrow xy y)
: product x y xy xy_to_x xy_to_y -> terminal x -> isomorphic xy y.
Proof.
  unfold terminal.
  clean.
  fact (H0 y).
  clean.
  assert (product x y y x0 id).
  - clear H1.
    unfold product.
    clean.
    unfold universal.
    split.
    + unfold arrowExists.
      exists qy.
      split; magic.
      specialize (H0 z).
      magic.
    + unfold arrowUnique.
      magic.
  - fact (productUnique C x y).
    unfold uniqueUpToIsomorphism in H3.
    specialize (H3 xy y).
    eMagic.
Qed.

#[export] Hint Resolve productTerminal : main.

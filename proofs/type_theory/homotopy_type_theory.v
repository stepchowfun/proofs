(****************************************************************)
(****************************************************************)
(****                                                        ****)
(****   A formalization of the function extensionality and   ****)
(****   univalence axioms                                    ****)
(****                                                        ****)
(****************************************************************)
(****************************************************************)

Require Import Stdlib.Program.Basics.

#[local] Open Scope program_scope.
#[local] Open Scope type.

(* A universe to be univalent *)

Definition U := Type.

(* The groupoid structure of types *)

Definition inv [A] [x y : A] (p : x = y) : y = x :=
  match p in _ = z return z = x with
  | eq_refl => eq_refl
  end.

Definition concat [A] [x y z : A] (p : x = y) (q : y = z) : x = z :=
  match q in _ = z return x = z with
  | eq_refl => p
  end.

Definition left_refl [A] [x y : A] (p : x = y) : concat eq_refl p = p :=
  match p return concat eq_refl p = p with
  | eq_refl => eq_refl
  end.

Definition right_refl [A] [x y : A] (p : x = y) : concat p eq_refl = p :=
  eq_refl.

Definition left_inv [A] [x y : A] (p : x = y) : concat (inv p) p = eq_refl :=
  match p return concat (inv p) p = eq_refl with
  | eq_refl => eq_refl
  end.

Definition right_inv [A] [x y : A] (p : x = y) : concat p (inv p) = eq_refl :=
  match p return concat p (inv p) = eq_refl with
  | eq_refl => eq_refl
  end.

Definition assoc [A] [x y z w : A] (p : x = y) (q : y = z) (r : z = w) :
  concat (concat p q) r = concat p (concat q r) :=
  match r return concat (concat p q) r = concat p (concat q r) with
  | eq_refl =>
    match q return concat p q = concat p q with
    | eq_refl => eq_refl
    end
  end.

(* Transport *)

Definition transport [A] [x y : A] [P : A -> Type] (p : x = y) (px : P x) : P y
:=
  match p in _ = z return P z with
  | eq_refl => px
  end.

(* Action on paths *)

Definition ap [A B] [x y : A] (f : A -> B) (p : x = y) : f x = f y :=
  match p in _ = z return f x = f z with
  | eq_refl => eq_refl
  end.

Definition ap_refl [A B] (x : A) (f : A -> B) :
  ap f eq_refl = @eq_refl _ (f x)
:= eq_refl.

Definition ap_concat [A B] [x y z : A] (f : A -> B) (p : x = y) (q : y = z) :
  ap f (concat p q) = concat (ap f p) (ap f q)
:=
  match q with
  | eq_refl => eq_refl
  end.

Definition ap_inv [A B] [x y : A] (f : A -> B) (p : x = y) :
  ap f (inv p) = inv (ap f p)
:=
  match p with
  | eq_refl => eq_refl
  end.

Definition ap_comp [A B C] [x y : A] (f : A -> B) (g : B -> C) (p : x = y) :
  ap g (ap f p) = ap (g ∘ f) p
:=
  match p with
  | eq_refl => eq_refl
  end.

Definition ap_id [A] [x y : A] (p : x = y) : ap id p = p
:=
  match p with
  | eq_refl => eq_refl
  end.

(* Homotopies *)

Definition Homotopy [A] [B : A -> Type] (f g : forall x : A, B x) :=
  forall x, f x = g x.

Definition path_to_homotopy [A] [B : A -> Type] [f g : forall x : A, B x]
  (p : f = g) : Homotopy f g
:=
  fun x =>
    match p in _ = h return f x = h x with
    | eq_refl => eq_refl
    end.

Definition naturality
  [A B]
  [x y : A]
  (f g : A -> B)
  (h : Homotopy f g)
  (p : x = y)
: concat (ap f p) (h y) = concat (h x) (ap g p)
:=
  match p in _ = z return concat (ap f p) (h z) = concat (h x) (ap g p) with
  | eq_refl => left_refl _
  end.

(* Equivalences *)

Definition IsEquiv [A B] (f : A -> B) := {
  g : B -> A & {
  eta : Homotopy (g ∘ f) id & {
  epsilon : Homotopy (f ∘ g) id &
  forall x, ap f (eta x) = epsilon (f x) }}}.

Definition path_to_equiv [A B] (p : A = B) :
  { f : A -> B & IsEquiv f } :=
  existT (@IsEquiv A B) (transport p)
    match p with
    | eq_refl =>
      existT _ id (
        existT _ (@eq_refl _) (existT _ (@eq_refl _) (fun _ => eq_refl))
      )
    end.

(* Univalence *)

Axiom univalence : forall A B : U, IsEquiv (@path_to_equiv A B).

(* Function extensionality *)

Axiom function_extensionality :
  forall (A : U) (B : A -> U) (f g : forall x : A, B x),
  IsEquiv (@path_to_homotopy _ _ f g).

(* Homotopy n-types (starting at 0 rather than the more conventional -2) *)

Fixpoint IsTrunc n (A : Type) :=
  match n with
  | O => { c : A & forall x, c = x }
  | S p => forall x y : A, IsTrunc p (x = y)
  end.

Definition IsContr := IsTrunc 0.
Definition IsProp := IsTrunc 1.
Definition IsSet := IsTrunc 2.

Theorem is_trunc_cumulative : forall n A, IsTrunc n A -> IsTrunc (1 + n) A.
Proof.
  induction n.
  - unfold IsTrunc.
    cbn.
    intros.
    destruct X.
    exists (eq_trans (eq_sym (e x)) (e y)).
    intro.
    destruct x1, (e x).
    reflexivity.
  - cbn in *.
    intros.
    apply IHn.
    apply X.
Qed.

Theorem proof_irrelevance_is_prop :
  forall A, (forall x y : A, x = y) -> IsProp A.
Proof.
  unfold IsProp, IsTrunc.
  intros.
  exists (H x y).
  destruct x0.
  assert (forall x y (p : x = y), H x y = concat p (H y y)).
  - intros.
    destruct p.
    rewrite left_refl.
    reflexivity.
  - specialize (H0 _ _ (H x x)).
    assert (
      forall (x y z : A) (p : x = y) (q r : y = z),
      concat p q = concat p r -> q = r
    ).
    + intros.
      destruct p.
      do 2 rewrite left_refl in H1.
      assumption.
    + specialize (H1 _ _ _ (H x x) (H x x) eq_refl).
      auto.
Qed.

Theorem is_truncated_is_prop : forall n A, IsProp (IsTrunc n A).
Proof.
  induction n; intros; apply proof_irrelevance_is_prop; intros.
  - unfold IsTrunc in *.
    destruct x, y.
    destruct (e0 x).
    assert (e = e0).
    + assert (IsProp A).
      * apply proof_irrelevance_is_prop.
        intros.
        rewrite <- (e x).
        rewrite <- (e y).
        reflexivity.
      * destruct (function_extensionality _ _ e e0).
        destruct s.
        apply x.
        unfold Homotopy.
        intro.
        pose proof (is_trunc_cumulative 1 A X).
        destruct (X0 x0 x2 (e x2) (e0 x2)).
        auto.
    + rewrite H.
      reflexivity.
  - destruct (function_extensionality _ _ x y).
    destruct s.
    apply x0.
    unfold Homotopy.
    intro.
    destruct (function_extensionality _ _ (x x2) (y x2)).
    destruct s.
    apply x3.
    unfold Homotopy.
    intro.
    apply IHn.
Qed.

(* Quasi-inverses *)

Definition QuasiInv [A B] (f : A -> B) :=
  { g : B -> A & Homotopy (g ∘ f) id * Homotopy (f ∘ g) id }.

Theorem quasi_inv_is_equiv :
  forall A B (f : A -> B), QuasiInv f -> IsEquiv f.
Proof.
  intros.
  destruct X, p.
  rename x into g.
  rename h into eta.
  rename h0 into epsilon.
  exists g.
  exists eta.
  exists (fun y =>
    concat (inv (epsilon (f (g y)))) (concat (ap f (eta (g y))) (epsilon y))
  ).
  intro.
  replace (eta (g (f x))) with (ap (g ∘ f) (eta x)).
  - replace (
      concat
        (@ap A B ((g ∘ f) (g (f x))) (@id A (g (f x))) f
          (@ap A A ((g ∘ f) x) (@id A x) (g ∘ f) (eta x)))
        (epsilon (f x))
    ) with (concat (epsilon (f (g (f x)))) (ap f (eta x))).
    + rewrite <- assoc.
      rewrite left_inv.
      rewrite left_refl.
      reflexivity.
    + pose proof naturality.
      specialize H with (h := fun x => epsilon (f x)) (p := eta x).
      unfold id, compose in *.
      change (ap f (eta x)) with (ap (fun x : A => f x) (eta x)).
      rewrite <- H.
      rewrite (ap_comp (fun x0 : A => g (f x0)) f).
      reflexivity.
  - change (g (f x)) with ((g ∘ f) x).
    pose proof naturality.
    specialize H with (h := eta) (p := eta x).
    change (eta (id x)) with (eta x) in H.
    replace (ap id (eta x)) with (eta x) in H.
    + assert (
        concat (concat (ap (g ∘ f) (eta x)) (eta x)) (inv (eta x)) =
        concat (concat (eta ((g ∘ f) x)) (eta x)) (inv (eta x))
      ).
      * unfold id.
        unfold id in H.
        rewrite H.
        reflexivity.
      * do 2 rewrite assoc in H0.
        do 2 rewrite right_inv in H0.
        exact H0.
    + set (p := eta x).
      destruct p.
      reflexivity.
Qed.

Definition equiv_is_quasi_inv A B (f : A -> B) (e : IsEquiv f) : QuasiInv f
:= existT _ (projT1 e) (projT1 (projT2 e), projT1 (projT2 (projT2 e))).

(* Equivalences form a category. *)

Theorem id_is_equiv : forall A, IsEquiv (@id A).
Proof.
  intro.
  unfold IsEquiv.
  exists id.
  exists (fun _ => eq_refl).
  exists (fun _ => eq_refl).
  reflexivity.
Qed.

Theorem comp_is_equiv :
  forall A B C (f : A -> B) (g : B -> C),
  IsEquiv f ->
  IsEquiv g ->
  IsEquiv (g ∘ f).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  destruct X, X0.
  exists (x ∘ x0).
  do 2 destruct s, s0.
  unfold id, compose in *.
  split; intro.
  - rewrite x2.
    rewrite x1.
    reflexivity.
  - rewrite x3.
    rewrite x4.
    reflexivity.
Qed.

(* Equivalence respect truncation. *)

Theorem equiv_trunc :
  forall n A B (f : A -> B), IsEquiv f -> IsTrunc n A -> IsTrunc n B.
Proof.
  intros.
  destruct (univalence A B).
  rewrite <- x; auto.
  exists f.
  assumption.
Qed.

(* Sigma types *)

Definition sigma_path [A] [B : A -> Type] (s1 s2 : sigT B) (h : s1 = s2)
: { p : projT1 s1 = projT1 s2 & transport p (projT2 s1) = projT2 s2 }
:=
  match h with
  | eq_refl => existT _ eq_refl eq_refl
  end.

Theorem sigma_path_is_equiv :
  forall A (B : A -> Type) (s1 s2 : sigT B), IsEquiv (sigma_path s1 s2).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  exists (
    match s1
    return
      { p : projT1 s1 = projT1 s2 & transport p (projT2 s1) = projT2 s2 } ->
      s1 = s2
    with
    | existT _ s1_1 s1_2 =>
      match s2
      return
        { p : s1_1 = projT1 s2 & transport p s1_2 = projT2 s2 } ->
        existT _ s1_1 s1_2 = s2
      with
      | existT _ s2_1 s2_2 =>
        fun p =>
          match projT1 p
          as q
          in _ = z
          return
            forall s2_2 : B z,
            transport q s1_2 = projT2 (existT B z s2_2) ->
            existT _ s1_1 s1_2 = existT _ z s2_2
          with
          | eq_refl =>
            fun s2_2 h =>
              match h with
              | eq_refl => eq_refl
              end
          end s2_2 (projT2 p)
      end
    end
  ).
  split; intro.
  - destruct x, s1.
    reflexivity.
  - destruct x, s1, s2.
    cbn in x, e.
    destruct x, e.
    reflexivity.
Qed.

(* Homotopy fibers *)

Definition fiber [A B] (f : A -> B) y := { x & f x = y }.

Definition fiber_component_path [A B] [f : A -> B] [y] (f1 f2 : fiber f y)
  (g : { p : projT1 f1 = projT1 f2 & transport p (projT2 f1) = projT2 f2 })
: { p : projT1 f1 = projT1 f2 & concat (ap f p) (projT2 f2) = projT2 f1 }
:=
  existT _ (projT1 g) (
    match projT1 g
    as g1
    return
      forall p2_2 (g2 : transport g1 (projT2 f1) = p2_2),
      concat (ap f g1) p2_2 = projT2 f1
    with
    | eq_refl => fun p2_2 g2 => concat (left_refl p2_2) (inv g2)
    end (projT2 f2) (projT2 g)
  ).

Theorem fiber_component_path_is_equiv :
  forall A B (f : A -> B) y (f1 f2 : fiber f y),
  IsEquiv (fiber_component_path f1 f2).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  exists (
    fun g =>
      existT _ (projT1 g) (
        match projT1 g
        as p
        in _ = fx_1
        return
          forall (q : f fx_1 = y) (g2 : concat (ap f p) q = projT2 f1),
          transport p (projT2 f1) = q
        with
        | eq_refl =>
          fun f2_2 g2 =>
            match left_refl f2_2 in _ = z return projT2 f1 = z with
            | eq_refl => inv g2
            end
        end (projT2 f2) (projT2 g)
      )
  ).
  split; intro; destruct x, f1, f2; cbn in x, e.
  - destruct x, e, e0.
    reflexivity.
  - destruct x, e, e1.
    reflexivity.
Qed.

Definition fiber_path [A B] [f : A -> B] [y] (f1 f2 : fiber f y)
: f1 = f2 ->
  { p : projT1 f1 = projT1 f2 & concat (ap f p) (projT2 f2) = projT2 f1 }
:= (fiber_component_path f1 f2) ∘ (sigma_path f1 f2).

Theorem fiber_path_is_equiv :
  forall A B (f : A -> B) y (f1 f2 : fiber f y), IsEquiv (fiber_path f1 f2).
Proof.
  intros.
  unfold fiber_path.
  apply comp_is_equiv.
  - apply sigma_path_is_equiv.
  - apply fiber_component_path_is_equiv.
Qed.

Theorem fiber_is_contr :
  forall A B (f : A -> B) y, IsEquiv f -> IsContr (fiber f y).
Proof.
  intros.
  unfold IsContr, IsTrunc.
  destruct X.
  do 2 destruct s.
  exists (existT _ (x y) (x1 y)).
  intros.
  destruct x2.
  pose proof fiber_path_is_equiv.
  specialize X with
    (f1 := existT (fun x3 : A => f x3 = y) (x y) (x1 y))
    (f2 := existT (fun x3 : A => f x3 = y) x2 e0).
  destruct X.
  apply x3.
  exists (concat (ap x (inv e0)) (x0 x2)).
  cbn.
  rewrite ap_concat.
  specialize (e x2).
  unfold id, compose in *.
  rewrite e.
  rewrite ap_comp.
  pose proof naturality.
  specialize H with (h := x1) (p := inv e0).
  unfold id, compose in *.
  rewrite H.
  rewrite assoc.
  rewrite ap_id.
  rewrite left_inv.
  reflexivity.
Qed.

(* Left and right inverses of equivalences are contractible. *)

Definition linv [A B] (f : A -> B) := { g & Homotopy (g ∘ f) id }.

Definition rinv [A B] (f : A -> B) := { g & Homotopy (f ∘ g) id }.

Theorem precompose_is_equiv :
  forall A B C (f : B -> C),
  IsEquiv f ->
  IsEquiv (fun g : A -> B => f ∘ g).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  destruct X.
  do 2 destruct s.
  exists (fun h : A -> C => x ∘ h).
  unfold id, compose in *.
  split; intro.
  - destruct (function_extensionality _ _ (fun x3 : A => x (f (x2 x3))) x2).
    do 2 destruct s.
    apply x3.
    intro.
    rewrite x0.
    reflexivity.
  - destruct (function_extensionality _ _ (fun x3 : A => f (x (x2 x3))) x2).
    do 2 destruct s.
    apply x3.
    intro.
    rewrite x1.
    reflexivity.
Qed.

Theorem postcompose_is_equiv :
  forall A B C (f : A -> B),
  IsEquiv f ->
  IsEquiv (fun g : B -> C => g ∘ f).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  destruct X.
  do 2 destruct s.
  exists (fun h : A -> C => h ∘ x).
  unfold id, compose in *.
  split; intro.
  - destruct (function_extensionality _ _ (fun x3 : B => x2 (f (x x3))) x2).
    do 2 destruct s.
    apply x3.
    intro.
    rewrite x1.
    reflexivity.
  - destruct (function_extensionality _ _ (fun x3 : A => x2 (x (f x3))) x2).
    do 2 destruct s.
    apply x3.
    intro.
    rewrite x0.
    reflexivity.
Qed.

Definition to_linv [A B] [f : A -> B] (li : { g : B -> A & g ∘ f = id })
: linv f
:=
  existT
    (fun g => Homotopy (g ∘ f) id)
    (projT1 li)
    (path_to_homotopy (projT2 li)).

Definition to_rinv [A B] [f : A -> B] (ri : { g : B -> A & f ∘ g = id })
: rinv f
:=
  existT
    (fun g => Homotopy (f ∘ g) id)
    (projT1 ri)
    (path_to_homotopy (projT2 ri)).

Theorem to_linv_is_equiv :
  forall A B (f : A -> B), IsEquiv (@to_linv _ _ f).
Proof.
  unfold to_linv.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  exists (
    fun li =>
      existT
        (fun g => g ∘ f = id)
        (projT1 li)
        (projT1
          (function_extensionality _ _ ((projT1 li) ∘ f) id) (projT2 li))
  ).
  split; intro.
  - unfold compose, id in *.
    destruct x.
    cbn.
    destruct e.
    set (fe :=
      function_extensionality _ _
        (fun x0 : A => x (f x0))
        (fun x0 : A => x (f x0))
    ).
    destruct fe.
    do 2 destruct s.
    cbn.
    unfold compose in x1.
    rewrite x1.
    reflexivity.
  - unfold compose, id in *.
    destruct x.
    cbn.
    set (fe :=
      function_extensionality _ _
        (fun x0 : A => x (f x0))
        (fun x0 : A => x0)
    ).
    destruct fe.
    do 2 destruct s.
    cbn.
    unfold compose in x2.
    rewrite x2.
    reflexivity.
Qed.

Theorem to_rinv_is_equiv :
  forall A B (f : A -> B), IsEquiv (@to_rinv _ _ f).
Proof.
  unfold to_rinv.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  exists (
    fun li =>
      existT
        (fun g => f ∘ g = id)
        (projT1 li)
        (projT1
          (function_extensionality _ _ (f ∘ (projT1 li)) id) (projT2 li))
  ).
  split; intro.
  - unfold compose, id in *.
    destruct x.
    cbn.
    destruct e.
    set (fe :=
      function_extensionality _ _
        (fun x0 : B => f (x x0))
        (fun x0 : B => f (x x0))
    ).
    destruct fe.
    do 2 destruct s.
    cbn.
    unfold compose in x1.
    rewrite x1.
    reflexivity.
  - unfold compose, id in *.
    destruct x.
    cbn.
    set (fe :=
      function_extensionality _ _
        (fun x0 : B => f (x x0))
        (fun x0 : B => x0)
    ).
    destruct fe.
    do 2 destruct s.
    cbn.
    unfold compose in x2.
    rewrite x2.
    reflexivity.
Qed.

Theorem linv_is_contr : forall A B (f : A -> B), IsEquiv f -> IsContr (linv f).
Proof.
  intros.
  apply equiv_trunc with (f := @to_linv _ _ f); auto.
  - apply to_linv_is_equiv.
  - apply fiber_is_contr with (f := fun g : B -> A => g ∘ f) (y := id).
    apply postcompose_is_equiv.
    assumption.
Qed.

Theorem rinv_is_contr : forall A B (f : A -> B), IsEquiv f -> IsContr (rinv f).
Proof.
  intros.
  apply equiv_trunc with (f := @to_rinv _ _ f); auto.
  - apply to_rinv_is_equiv.
  - apply fiber_is_contr with (f := fun g : B -> A => f ∘ g) (y := id).
    apply precompose_is_equiv.
    assumption.
Qed.

(* An example of using univalence *)

Inductive Bit : U :=
| Zero
| One.

Inductive Weekend : U :=
| Saturday
| Sunday.

Definition weekend_to_bit x :=
  match x with
  | Saturday => Zero
  | Sunday => One
  end.

Definition bit_to_weekend x :=
  match x with
  | Zero => Saturday
  | One => Sunday
  end.

Theorem weekend_bit_equiv : IsEquiv weekend_to_bit.
Proof.
  apply quasi_inv_is_equiv.
  exists bit_to_weekend.
  split; intro; destruct x; reflexivity.
Qed.

Definition weekend_bit_path : Weekend = Bit :=
  projT1 (univalence _ _) (existT _ _ weekend_bit_equiv).

Definition invert_weekend x :=
  match x with
  | Saturday => Sunday
  | Sunday => Saturday
  end.

Theorem invert_weekend_involution x : invert_weekend (invert_weekend x) = x.
Proof.
  destruct x; auto.
Qed.

Definition invert_weekend_with_theorem :=
  exist (fun invert => forall x, invert (invert x) = x)
    invert_weekend
    invert_weekend_involution.

Definition invert_bit_with_theorem :=
  match weekend_bit_path in _ = A
  return { invert : A -> A | forall x, invert (invert x) = x } with
  | eq_refl => invert_weekend_with_theorem
  end.

Definition invert_bit : Bit -> Bit :=
  proj1_sig invert_bit_with_theorem.

Definition invert_bit_involution : forall x, invert_bit (invert_bit x) = x :=
  proj2_sig invert_bit_with_theorem.

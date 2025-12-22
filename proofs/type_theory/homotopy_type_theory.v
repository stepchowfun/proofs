(****************************************************)
(****************************************************)
(****                                            ****)
(****   An exploration of homotopy type theory   ****)
(****                                            ****)
(****************************************************)
(****************************************************)

Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Program.Basics.

#[local] Open Scope program_scope.
#[local] Open Scope type.

Set Universe Polymorphism.

(* A universe to be univalent *)

Definition U := Type.

(* The groupoid structure of types *)

Definition inv [A] [x y : A] (p : x = y) : y = x :=
  match p with
  | eq_refl => eq_refl
  end.

Definition inv_refl [A] (x : A) : inv (@eq_refl A x) = @eq_refl A x :=
  eq_refl.

Definition inv_inv [A] [x y : A] (p : x = y) : inv (inv p) = p :=
  match p with
  | eq_refl => eq_refl
  end.

Definition concat [A] [x y z : A] (p : x = y) (q : y = z) : x = z :=
  match q with
  | eq_refl => p
  end.

Definition left_refl [A] [x y : A] (p : x = y) : concat eq_refl p = p :=
  match p with
  | eq_refl => eq_refl
  end.

Definition right_refl [A] [x y : A] (p : x = y) : concat p eq_refl = p :=
  eq_refl.

Definition left_inv [A] [x y : A] (p : x = y) : concat (inv p) p = eq_refl :=
  match p with
  | eq_refl => eq_refl
  end.

Definition right_inv [A] [x y : A] (p : x = y) : concat p (inv p) = eq_refl :=
  match p with
  | eq_refl => eq_refl
  end.

Definition assoc [A] [x y z w : A] (p : x = y) (q : y = z) (r : z = w) :
  concat (concat p q) r = concat p (concat q r) :=
  match r with
  | eq_refl =>
    match q with
    | eq_refl => eq_refl
    end
  end.

(* Functorial action on paths *)

Definition ap [A B] [x y : A] (f : A -> B) (p : x = y) : f x = f y :=
  match p with
  | eq_refl => eq_refl
  end.

Definition ap_refl [A B] (x : A) (f : A -> B) : ap f eq_refl = @eq_refl _ (f x)
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

Definition ap_id [A] [x y : A] (p : x = y) : ap id p = p :=
  match p with
  | eq_refl => eq_refl
  end.

Definition ap_compose [A B C] [x y : A] (f : A -> B) (g : B -> C) (p : x = y) :
  ap g (ap f p) = ap (g ∘ f) p
:=
  match p with
  | eq_refl => eq_refl
  end.

(* Transport *)

Definition transport [A] [x y : A] [P : A -> Type] (p : x = y) (px : P x) : P y
:=
  match p with
  | eq_refl => px
  end.

Definition transport_refl [A] [P : A -> Type] [x : A] (u : P x)
: transport eq_refl u = u
:= eq_refl.

Definition transport_concat
  [A] [P : A -> Type] [x y z : A] (p : x = y) (q : y = z) (u : P x)
: transport q (transport p u) = transport (concat p q) u
:=
  match q with
  | eq_refl => eq_refl
  end.

Definition transport_const [A B] [x y : A] (p : x = y) (z : B)
: transport p z = z
:=
  match p with
  | eq_refl => eq_refl
  end.

Definition transport_compose
  [A B] [P : B -> Type] [x y : A] (p : x = y) (f : A -> B)
: transport (P := compose P f) p = transport (ap f p)
:=
  match p with
  | eq_refl => eq_refl
  end.

Definition transport_function
  [A] [B C : A -> Type] [x y : A]
  (p : x = y) (f : forall x, B x -> C x) (u : B x)
: transport p (f x u) = f y (transport p u)
:=
  match p with
  | eq_refl => eq_refl
  end.

(* Homotopies *)

Definition Homotopy [A] [B : A -> Type] (f g : forall x, B x) :=
  forall x, f x = g x.

Definition naturality
  [A B]
  [x y : A]
  [f g : A -> B]
  (h : Homotopy f g)
  (p : x = y)
: concat (ap f p) (h y) = concat (h x) (ap g p)
:=
  match p with
  | eq_refl => left_refl _
  end.

(* Equivalences *)

Definition IsEquiv [A B] (f : A -> B) := {
  g : B -> A & {
  eta : Homotopy (g ∘ f) id & {
  epsilon : Homotopy (f ∘ g) id &
  forall x, ap f (eta x) = epsilon (f x) }}}.

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
      rewrite (ap_compose (fun x0 : A => g (f x0)) f).
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
      * unfold id in *.
        rewrite H.
        reflexivity.
      * do 2 rewrite assoc in H0.
        do 2 rewrite right_inv in H0.
        exact H0.
    + set (p := eta x).
      destruct p.
      reflexivity.
Qed.

Definition equiv_is_quasi_inv [A B] [f : A -> B] (e : IsEquiv f) : QuasiInv f
:= existT _ (projT1 e) (projT1 (projT2 e), projT1 (projT2 (projT2 e))).

(*
  The groupoid structure of equivalences implies that type equivalence is an
  equivalence relation on the universe.
*)

Theorem id_is_equiv : forall A, IsEquiv (@id A).
Proof.
  intro.
  unfold IsEquiv.
  exists id.
  do 2 exists (fun _ => eq_refl).
  reflexivity.
Qed.

Theorem comp_is_equiv :
  forall A B C (f : A -> B) (g : B -> C),
  IsEquiv f -> IsEquiv g -> IsEquiv (g ∘ f).
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

Theorem inv_is_equiv :
  forall A B (f : A -> B) (e : IsEquiv f), IsEquiv (projT1 e).
Proof.
  intros.
  destruct e.
  cbn.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  exists f.
  do 2 destruct s.
  auto.
Qed.

(* The path space of the empty type *)

Definition empty_path_intro (x y : Empty_set) : Empty_set -> x = y :=
  match x with end.

Definition empty_path_elim [x y : Empty_set] : x = y -> Empty_set :=
  match x with end.

Definition empty_path_compute (x y : Empty_set)
: forall c, empty_path_elim (empty_path_intro x y c) = c
:= match x with end.

Definition empty_path_unique (x y : Empty_set)
: forall p, empty_path_intro x y (empty_path_elim p) = p
:= match x with end.

Theorem empty_path_intro_is_equiv :
  forall x y : Empty_set, IsEquiv (empty_path_intro x y).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  exists (@empty_path_elim x y).
  split; intro.
  - exact (empty_path_compute _ _ x0).
  - exact (empty_path_unique _ _ x0).
Qed.

Theorem empty_path_elim_is_equiv :
  forall x y : Empty_set, IsEquiv (@empty_path_elim x y).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  exists (@empty_path_intro x y).
  split; intro.
  - exact (empty_path_unique _ _ x0).
  - exact (empty_path_compute _ _ x0).
Qed.

Theorem empty_path_refl : forall x c, eq_refl = empty_path_intro x x c.
Proof.
  destruct x.
Qed.

Theorem empty_path_compose :
  forall x y z c (p : x = y) (q : y = z), concat p q = empty_path_intro x z c.
Proof.
  destruct x.
Qed.

Theorem empty_path_inv :
  forall x y c (p : x = y), inv p = empty_path_intro y x c.
Proof.
  destruct x.
Qed.

Theorem empty_transport :
  forall A (x y : A) (p : x = y) (u : Empty_set), transport p u = u.
Proof.
  intros.
  apply transport_const.
Qed.

(* The path space of the unit type *)

Definition unit_path_intro (x y : unit) : unit -> x = y :=
  fun _ =>
    match x with
    | tt =>
      match y with
      | tt => eq_refl
      end
    end.

Definition unit_path_elim [x y : unit] : x = y -> unit :=
  fun _ => tt.

Definition unit_path_compute (x y : unit)
: forall c, unit_path_elim (unit_path_intro x y c) = c
:=
  fun c =>
    match c with
    | tt => eq_refl
    end.

Definition unit_path_unique (x y : unit)
: forall p, unit_path_intro x y (unit_path_elim p) = p
:=
  fun p =>
    match p with
    | eq_refl =>
      match x with
      | tt => eq_refl
      end
    end.

Theorem unit_path_intro_is_equiv : forall x y, IsEquiv (unit_path_intro x y).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  exists (@unit_path_elim x y).
  split; intro.
  - exact (unit_path_compute _ _ x0).
  - exact (unit_path_unique _ _ x0).
Qed.

Theorem unit_path_elim_is_equiv : forall x y, IsEquiv (@unit_path_elim x y).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  exists (@unit_path_intro x y).
  split; intro.
  - exact (unit_path_unique _ _ x0).
  - exact (unit_path_compute _ _ x0).
Qed.

Theorem unit_path_refl : forall x c, eq_refl = unit_path_intro x x c.
Proof.
  destruct x.
  reflexivity.
Qed.

Theorem unit_path_compose :
  forall x y z c (p : x = y) (q : y = z), concat p q = unit_path_intro x z c.
Proof.
  destruct p, q, x.
  reflexivity.
Qed.

Theorem unit_path_inv :
  forall x y c (p : x = y), inv p = unit_path_intro y x c.
Proof.
  destruct p, x.
  reflexivity.
Qed.

Theorem unit_transport :
  forall A (x y : A) (p : x = y) (u : unit), transport p u = u.
Proof.
  intros.
  apply transport_const.
Qed.

(* The path space of the Boolean type *)

Definition bool_code x y := if eqb x y then unit else Empty_set.

Definition bool_path_intro (x y : bool) : bool_code x y -> x = y :=
  match x return bool_code x y -> x = y with
  | true =>
    match y return bool_code true y -> true = y with
    | true => fun c => eq_refl
    | false => fun c => match c with end
    end
  | false =>
    match y return bool_code false y -> false = y with
    | true => fun c => match c with end
    | false => fun c => eq_refl
    end
  end.

Definition bool_path_elim [x y : bool] : x = y -> bool_code x y :=
  fun p =>
    match p with
    | eq_refl =>
      match x with
      | true => tt
      | false => tt
      end
    end.

Definition bool_path_compute (x y : bool)
: forall c, bool_path_elim (bool_path_intro x y c) = c
:=
  match x with
  | true =>
    match y with
    | true => fun c => match c with tt => eq_refl end
    | false => fun c => match c with end
    end
  | false =>
    match y with
    | true => fun c => match c with end
    | false => fun c => match c with tt => eq_refl end
    end
  end.

Definition bool_path_unique (x y : bool)
: forall p, bool_path_intro x y (bool_path_elim p) = p
:=
  fun p =>
    match p with
    | eq_refl =>
      match x with
      | true => eq_refl
      | false => eq_refl
      end
    end.

Theorem bool_path_intro_is_equiv :
  forall x y : bool, IsEquiv (bool_path_intro x y).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  exists (@bool_path_elim x y).
  split; intro.
  - exact (bool_path_compute _ _ x0).
  - exact (bool_path_unique _ _ x0).
Qed.

Theorem bool_path_elim_is_equiv :
  forall x y : bool, IsEquiv (@bool_path_elim x y).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  exists (@bool_path_intro x y).
  split; intro.
  - exact (bool_path_unique _ _ x0).
  - exact (bool_path_compute _ _ x0).
Qed.

Theorem bool_path_refl : forall x c, eq_refl = bool_path_intro x x c.
Proof.
  destruct x; reflexivity.
Qed.

Theorem bool_path_compose :
  forall x y z c (p : x = y) (q : y = z), concat p q = bool_path_intro x z c.
Proof.
  destruct p, q, x; reflexivity.
Qed.

Theorem bool_path_inv :
  forall x y c (p : x = y), inv p = bool_path_intro y x c.
Proof.
  destruct p, x; reflexivity.
Qed.

Theorem bool_transport :
  forall A (x y : A) (p : x = y) (u : bool), transport p u = u.
Proof.
  intros.
  apply transport_const.
Qed.

(* The path spaces of sigma types *)

Definition sigma_path_intro
  [A] [B : A -> Type] (s1 s2 : sigT B)
: { p : projT1 s1 = projT1 s2 & transport p (projT2 s1) = projT2 s2 } ->
  s1 = s2
:=
  match s1 with
  | existT _ s1_1 s1_2 =>
    match s2 with
    | existT _ s2_1 s2_2 =>
      fun h =>
        match projT1 h
        as q
        in _ = z
        return
          forall s2_2 : B z,
          transport q s1_2 = s2_2 ->
          existT _ s1_1 s1_2 = existT _ z s2_2
        with
        | eq_refl =>
          fun _ i =>
            match i with
            | eq_refl => eq_refl
            end
        end s2_2 (projT2 h)
    end
  end.

Definition sigma_path_elim [A] [B : A -> Type] [s1 s2 : sigT B] (h : s1 = s2)
: { p : projT1 s1 = projT1 s2 & transport p (projT2 s1) = projT2 s2 }
:=
  match h with
  | eq_refl => existT _ eq_refl eq_refl
  end.

Definition sigma_path_compute [A] [B : A -> Type] (s1 s2 : sigT B)
: forall h :
    { p : projT1 s1 = projT1 s2 & transport p (projT2 s1) = projT2 s2 },
  sigma_path_elim (sigma_path_intro s1 s2 h) = h
:=
  match s1 with
  | existT _ s1_1 s1_2 =>
    match s2 with
    | existT _ s2_1 s2_2 =>
      fun h =>
        match h with
        | existT _ h1 h2 =>
          match h1
          in _ = z
          return
            forall (s2_2 : B z) (h2 : transport h1 s1_2 = s2_2),
            sigma_path_elim (
              sigma_path_intro
                (existT _ s1_1 s1_2)
                (existT _ z s2_2)
                (existT _ h1 h2)
            ) = existT _ h1 h2
          with
          | eq_refl =>
            fun _ h2 =>
              match h2 with
              | eq_refl => eq_refl
              end
          end s2_2 h2
        end
    end
  end.

Definition sigma_path_unique
  [A] [B : A -> Type] [s1 s2 : sigT B] (p : s1 = s2)
: p = sigma_path_intro _ _ (sigma_path_elim p)
:=
  match p with
  | eq_refl =>
    match s1 with
    | existT _ _ _ => eq_refl
    end
  end.

Theorem sigma_path_intro_is_equiv :
  forall A (B : A -> Type) (s1 s2 : sigT B),
  IsEquiv (sigma_path_intro s1 s2).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  exists (@sigma_path_elim _ _ s1 s2).
  split; intro.
  - exact (sigma_path_compute _ _ x).
  - exact (inv (sigma_path_unique x)).
Qed.

Theorem sigma_path_elim_is_equiv :
  forall A (B : A -> Type) (s1 s2 : sigT B),
  IsEquiv (@sigma_path_elim _ _ s1 s2).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  exists (sigma_path_intro s1 s2).
  split; intro.
  - exact (inv (sigma_path_unique x)).
  - exact (sigma_path_compute _ _ x).
Qed.

Theorem sigma_path_refl :
  forall A (B : A -> Type) (s : sigT B),
  eq_refl = sigma_path_intro s s (existT _ eq_refl eq_refl).
Proof.
  intros.
  apply sigma_path_unique.
Qed.

Theorem sigma_path_compose :
  forall A (B : A -> Type) (s1 s2 s3 : sigT B) (p : s1 = s2) (q : s2 = s3),
  concat p q =
  sigma_path_intro s1 s3 (
    existT _
      (concat (projT1 (sigma_path_elim p)) (projT1 (sigma_path_elim q)))
      (
        transport
          (P := fun r =>
            transport (
              concat (projT1 (sigma_path_elim p)) (projT1 (sigma_path_elim q))
            ) (projT2 s1) = r
          )
          (projT2 (sigma_path_elim q))
          (
            transport
              (P := fun r =>
                transport (
                  concat
                    (projT1 (sigma_path_elim p))
                    (projT1 (sigma_path_elim q))
                ) (projT2 s1) = transport (projT1 (sigma_path_elim q)) r
              )
              (projT2 (sigma_path_elim p))
              (
                inv (
                  transport_concat
                    (projT1 (sigma_path_elim p))
                    (projT1 (sigma_path_elim q))
                    (projT2 s1)
                )
              )
          )
      )
  ).
Proof.
  destruct p, q.
  apply sigma_path_unique.
Qed.

Theorem sigma_path_inv :
  forall A (B : A -> Type) (s1 s2 : sigT B) (p : s1 = s2),
  inv p = sigma_path_intro s2 s1 (
    existT _
      (inv (projT1 (sigma_path_elim p)))
      (
        transport
          (
            P := fun q =>
              transport (inv (projT1 (sigma_path_elim p))) (projT2 s2) =
              transport q (projT2 s1)
          )
          (right_inv (projT1 (sigma_path_elim p)))
          (
            transport
              (
                P := fun q =>
                  transport (inv (projT1 (sigma_path_elim p))) q =
                  transport
                    (
                      concat
                        (projT1 (sigma_path_elim p))
                        (inv (projT1 (sigma_path_elim p)))
                    )
                    (projT2 s1)
              )
              (projT2 (sigma_path_elim p))
              (
                transport_concat
                  (projT1 (sigma_path_elim p))
                  (inv (projT1 (sigma_path_elim p)))
                  (projT2 s1)
              )
          )
      )
  ).
Proof.
  destruct p.
  apply sigma_path_unique.
Qed.

Theorem sigma_transport :
  forall
    C (A : C -> Type) (B : sigT A -> Type)
    (x y : C) (p : x = y)
    (ab : { ax : A x & B (existT A x ax) }),
  transport (P := fun x => { ax : A x & B (existT A x ax) }) p ab =
  existT (fun py => B (existT A y py))
    (transport (P := A) p (projT1 ab))
    (transport (P := B)
      (sigma_path_intro
        (existT A x (projT1 ab))
        (existT A y (transport p (projT1 ab)))
        (existT _ p eq_refl)
      )
      (projT2 ab)
    ).
Proof.
  destruct p, ab.
  reflexivity.
Qed.

(* The path spaces of pair types *)

Definition pair A B := sigT (fun _ : A => B).

Definition pair_path_intro [A B] (s1 s2 : pair A B)
: pair (projT1 s1 = projT1 s2) (projT2 s1 = projT2 s2) -> s1 = s2
:=
  match s1 with
  | existT _ s1_1 s1_2 =>
    match s2 with
    | existT _ s2_1 s2_2 =>
      fun h =>
        match projT1 h
        in _ = z
        return
          existT _ s1_1 s1_2 = existT _ z s2_2
        with
        | eq_refl =>
          match projT2 h with
          | eq_refl => eq_refl
          end
        end
    end
  end.

Definition pair_path_elim [A B] [s1 s2 : pair A B] (h : s1 = s2)
: pair (projT1 s1 = projT1 s2) (projT2 s1 = projT2 s2)
:=
  match h with
  | eq_refl => existT _ eq_refl eq_refl
  end.

Definition pair_path_compute [A B] (s1 s2 : pair A B)
: forall h : pair (projT1 s1 = projT1 s2) (projT2 s1 = projT2 s2),
  pair_path_elim (pair_path_intro s1 s2 h) = h
:=
  match s1 with
  | existT _ s1_1 s1_2 =>
    match s2 with
    | existT _ s2_1 s2_2 =>
      fun h =>
        match h with
        | existT _ h1 h2 =>
          match h1
          in _ = z
          return
            pair_path_elim (
              pair_path_intro
                (existT _ s1_1 s1_2)
                (existT _ z s2_2)
                (existT _ h1 h2)
            ) = existT _ h1 h2
          with
          | eq_refl =>
            match h2 with
            | eq_refl => eq_refl
            end
          end
        end
    end
  end.

Definition pair_path_unique [A B] [s1 s2 : pair A B] (p : s1 = s2)
: p = pair_path_intro _ _ (pair_path_elim p)
:=
  match p with
  | eq_refl =>
    match s1 with
    | existT _ _ _ => eq_refl
    end
  end.

Theorem pair_path_intro_is_equiv :
  forall A B (s1 s2 : pair A B), IsEquiv (pair_path_intro s1 s2).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  exists (@pair_path_elim _ _ s1 s2).
  split; intro.
  - exact (pair_path_compute _ _ x).
  - exact (inv (pair_path_unique x)).
Qed.

Theorem pair_path_elim_is_equiv :
  forall A B (s1 s2 : pair A B), IsEquiv (@pair_path_elim _ _ s1 s2).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  exists (pair_path_intro s1 s2).
  split; intro.
  - exact (inv (pair_path_unique x)).
  - exact (pair_path_compute _ _ x).
Qed.

Theorem pair_path_refl :
  forall A B (s : pair A B),
  eq_refl = pair_path_intro s s (existT _ eq_refl eq_refl).
Proof.
  intros.
  apply pair_path_unique.
Qed.

Theorem pair_path_compose :
  forall A B (s1 s2 s3 : pair A B) (p : s1 = s2) (q : s2 = s3),
  concat p q =
  pair_path_intro s1 s3 (
    existT _
      (concat (projT1 (pair_path_elim p)) (projT1 (pair_path_elim q)))
      (concat (projT2 (pair_path_elim p)) (projT2 (pair_path_elim q)))
  ).
Proof.
  destruct p, q.
  apply pair_path_unique.
Qed.

Theorem pair_path_inv :
  forall A B (s1 s2 : pair A B) (p : s1 = s2),
  inv p = pair_path_intro s2 s1 (
    existT _
      (inv (projT1 (pair_path_elim p)))
      (inv (projT2 (pair_path_elim p)))
  ).
Proof.
  destruct p.
  apply pair_path_unique.
Qed.

Theorem pair_transport :
  forall
    C (A : C -> Type) (B : C -> Type)
    (x y : C) (p : x = y)
    (ab : pair (A x) (B x)),
  transport (P := fun x => pair (A x) (B x)) p ab =
  existT (fun py => B y)
    (transport (P := A) p (projT1 ab))
    (transport (P := B) p (projT2 ab)).
Proof.
  destruct p, ab.
  reflexivity.
Qed.

(* The path spaces of pi types *)

Definition pi_path_elim [A] [B : A -> Type] [f g : forall x, B x]
  (p : f = g) : Homotopy f g
:=
  fun x =>
    match p with
    | eq_refl => eq_refl
    end.

Axiom function_extensionality :
  forall (A : U) (B : A -> U) (f g : forall x : A, B x),
  IsEquiv (@pi_path_elim _ _ f g).

Definition pi_path_intro [A] [B : A -> Type] (f g : forall x, B x)
  (h : Homotopy f g) : f = g
:= projT1 (function_extensionality _ _ f g) h.

Theorem pi_path_intro_is_equiv :
  forall A (B : A -> Type) (f g : forall x : A, B x),
  IsEquiv (@pi_path_intro _ _ f g).
Proof.
  intros.
  apply inv_is_equiv.
Qed.

Definition pi_path_compute
  [A] [B : A -> Type] (f g : forall x : A, B x) (h : Homotopy f g)
: pi_path_elim (pi_path_intro _ _ h) = h
:= projT1 (projT2 (projT2 (function_extensionality _ _ f g))) h.

Definition pi_path_unique
  [A] [B : A -> Type] [f g : forall x : A, B x] (p : f = g)
: p = pi_path_intro _ _ (pi_path_elim p)
:= inv (projT1 (projT2 (function_extensionality _ _ f g)) p).

Theorem pi_path_refl :
  forall A (B : A -> Type) (f : forall x : A, B x),
  eq_refl = pi_path_intro f f (fun x => eq_refl).
Proof.
  intros.
  apply pi_path_unique.
Qed.

Theorem pi_path_compose :
  forall A (B : A -> Type) (f g h : forall x : A, B x) (p : f = g) (q : g = h),
  concat p q = pi_path_intro f h (
    fun x => concat (pi_path_elim p x) (pi_path_elim q x)
  ).
Proof.
  destruct p, q.
  apply pi_path_unique.
Qed.

Theorem pi_path_inv :
  forall A (B : A -> Type) (f g : forall x : A, B x) (p : f = g),
  inv p = pi_path_intro g f (fun x => inv (pi_path_elim p x)).
Proof.
  destruct p.
  apply pi_path_unique.
Qed.

Theorem pi_transport :
  forall
    C (A : C -> Type) (B : forall x, A x -> Type)
    (x y : C) (p : x = y)
    (f : forall z : A x, B x z),
  transport (P := fun x => forall z : A x, B x z) p f =
  fun ay : A y =>
    transport (P := fun w => B (projT1 w) (projT2 w))
      (
        inv (
          sigma_path_intro
            (existT A y _)
            (existT A x _)
            (existT _ (inv p) eq_refl)
        )
      )
      (f (transport (P := A) (inv p) ay)).
Proof.
  destruct p.
  reflexivity.
Qed.

(* The path spaces of function types *)

Definition function_path_elim [A B] [f g : A -> B] (p : f = g) : Homotopy f g
:= pi_path_elim p.

Definition function_path_intro [A B] (f g : A -> B) (h : Homotopy f g) : f = g
:= pi_path_intro f g h.

Theorem function_path_intro_is_equiv :
  forall A B (f g : A -> B), IsEquiv (@function_path_intro _ _ f g).
Proof.
  intros.
  exact (pi_path_intro_is_equiv _ _ _ _).
Qed.

Definition function_path_compute [A B] (f g : A -> B) (h : Homotopy f g)
: function_path_elim (function_path_intro _ _ h) = h
:= pi_path_compute f g h.

Definition function_path_unique
  [A B] [f g : A -> B] (p : f = g)
: p = function_path_intro _ _ (function_path_elim p)
:= pi_path_unique p.

Theorem function_path_refl :
  forall A B (f : A -> B),
  eq_refl = function_path_intro f f (fun x => eq_refl).
Proof.
  intros.
  exact (pi_path_refl _ _ _).
Qed.

Theorem function_path_compose :
  forall A B (f g h : A -> B) (p : f = g) (q : g = h),
  concat p q = function_path_intro f h (
    fun x => concat (function_path_elim p x) (function_path_elim q x)
  ).
Proof.
  intros.
  exact (pi_path_compose _ _ _ _ _ _ _).
Qed.

Theorem function_path_inv :
  forall A B (f g : A -> B) (p : f = g),
  inv p = function_path_intro g f (fun x => inv (function_path_elim p x)).
Proof.
  intros.
  exact (pi_path_inv _ _ _ _ _).
Qed.

Theorem function_transport :
  forall
    C (A : C -> Type) (B : C -> Type)
    (x y : C) (p : x = y)
    (f : A x -> B x),
  transport (P := fun x => A x -> B x) p f =
  fun ay : A y => transport (P := B) p (f (transport (P := A) (inv p) ay)).
Proof.
  destruct p.
  reflexivity.
Qed.

(* The path space of the universe *)

Definition type_path_elim [A B] (p : A = B) :
  { f : A -> B & IsEquiv f } :=
  existT (@IsEquiv A B) (transport p)
    match p with
    | eq_refl => id_is_equiv _
    end.

Axiom univalence : forall A B : U, IsEquiv (@type_path_elim A B).

Definition type_path_intro [A B] [f : A -> B] (f_equiv : IsEquiv f) : A = B
:= projT1 (univalence _ _) (existT _ f f_equiv).

Theorem type_path_intro_is_equiv :
  forall A B, IsEquiv (
    fun s : { f : A -> B & IsEquiv f } => type_path_intro (projT2 s)
  ).
Proof.
  intros.
  replace ( fun s : { f : A -> B & IsEquiv f } => type_path_intro (projT2 s))
    with (projT1 (univalence A B)).
  - apply inv_is_equiv.
  - apply pi_path_intro.
    intro.
    unfold type_path_intro.
    rewrite <- sigT_eta.
    reflexivity.
Qed.

Definition type_path_compute [A B] [f : A -> B] (f_equiv : IsEquiv f) :
  type_path_elim (type_path_intro f_equiv) = existT _ f f_equiv
:= projT1 (projT2 (projT2 (univalence _ _))) (existT _ f f_equiv).

Definition type_path_unique [A B] (p : A = B) :
  p = type_path_intro (projT2 (type_path_elim p))
:=
  match p with
  | eq_refl => inv (projT1 (projT2 (univalence _ _)) eq_refl)
  end.

Theorem type_transport A (B : A -> Type) (x y : A) (p : x = y)
: transport (P := B) p = projT1 (type_path_elim (ap B p)).
Proof.
  exact (transport_compose p B).
Qed.

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
      * apply pi_path_intro.
        intro.
        pose proof (is_trunc_cumulative 1 A X).
        destruct (H x0 x (e x) (e0 x)).
        auto.
    + rewrite H.
      reflexivity.
  - apply pi_path_intro.
    intro.
    apply pi_path_intro.
    intro.
    apply IHn.
Qed.

(* Equivalence respects truncation. *)

Theorem equiv_trunc :
  forall n A B (f : A -> B), IsEquiv f -> IsTrunc n A -> IsTrunc n B.
Proof.
  intros.
  rewrite <- (type_path_intro X).
  assumption.
Qed.

(* Homotopy fibers *)

Definition fiber [A B] (f : A -> B) y := { x & f x = y }.

Definition fiber_component_path_intro
  [A B]
  [f : A -> B]
  [y]
  (f1 f2 : fiber f y)
  (h : { p : projT1 f1 = projT1 f2 & concat (ap f p) (projT2 f2) = projT2 f1 })
: { p : projT1 f1 = projT1 f2 & transport p (projT2 f1) = projT2 f2 }
:=
  existT _ (projT1 h) (
    match projT1 h
    as p
    in _ = fx_1
    return
      forall (q : f fx_1 = y) (g2 : concat (ap f p) q = projT2 f1),
      transport p (projT2 f1) = q
    with
    | eq_refl =>
      fun f2_2 g2 =>
        match left_refl f2_2 with
        | eq_refl => inv g2
        end
    end (projT2 f2) (projT2 h)
  ).

Definition fiber_component_path_elim
  [A B]
  [f : A -> B]
  [y]
  (f1 f2 : fiber f y)
  (h : { p : projT1 f1 = projT1 f2 & transport p (projT2 f1) = projT2 f2 })
: { p : projT1 f1 = projT1 f2 & concat (ap f p) (projT2 f2) = projT2 f1 }
:=
  existT _ (projT1 h) (
    match projT1 h
    as g1
    return
      forall p2_2 (g2 : transport g1 (projT2 f1) = p2_2),
      concat (ap f g1) p2_2 = projT2 f1
    with
    | eq_refl => fun p2_2 g2 => concat (left_refl p2_2) (inv g2)
    end (projT2 f2) (projT2 h)
  ).

Definition fiber_component_path_compute
  [A B]
  [f : A -> B]
  [y]
  (f1 f2 : fiber f y)
  (h : { p : projT1 f1 = projT1 f2 & concat (ap f p) (projT2 f2) = projT2 f1 })
: fiber_component_path_elim _ _ (fiber_component_path_intro _ _ h) = h
:=
  match f1
  return
    forall h : {
      p : projT1 f1 = projT1 f2 &
      concat (ap f p) (projT2 f2) = projT2 f1
    },
    fiber_component_path_elim f1 f2
      (fiber_component_path_intro f1 f2 h) = h
  with
  | existT _ f1_1 f1_2 =>
    match f2
    return
      forall h : { p : f1_1 = projT1 f2 & concat (ap f p) (projT2 f2) = f1_2 },
      fiber_component_path_elim (existT _ f1_1 f1_2) f2
        (fiber_component_path_intro (existT _ f1_1 f1_2) f2 h) = h
    with
    | existT _ f2_1 f2_2 =>
      fun h =>
      match h
      return
        fiber_component_path_elim
          (existT _ f1_1 f1_2)
          (existT _ f2_1 f2_2)
          (fiber_component_path_intro
            (existT _ f1_1 f1_2)
            (existT _ f2_1 f2_2)
            h)
        = h
      with
      | existT _ h1 h2 =>
        match h1
        in _ = z
        return
          forall (f2_2 : f z = y) (h2 : concat (ap f h1) f2_2 = f1_2),
          fiber_component_path_elim
            (existT _ f1_1 f1_2)
            (existT _ z f2_2)
            (fiber_component_path_intro
              (existT _ f1_1 f1_2)
              (existT _ z f2_2)
              (existT _ h1 h2))
          = existT _ h1 h2
        with
        | eq_refl =>
          match f1_2
          in _ = z
          return
            forall
              (f2_2 : f f1_1 = z)
              (h2 : concat (ap f eq_refl) f2_2 = f1_2),
            fiber_component_path_elim
              (existT _ f1_1 f1_2)
              (existT _ f1_1 f2_2)
              (fiber_component_path_intro
                (existT _ f1_1 f1_2)
                (existT _ f1_1 f2_2)
                (existT _ eq_refl h2))
            = existT _ eq_refl h2
          with
          | eq_refl =>
            fun
              (f2_2 : f f1_1 = f f1_1)
              (h2 : concat (ap f eq_refl) f2_2 = eq_refl) =>
            match h2
            in _ = z
            return
              fiber_component_path_elim
                (existT _ f1_1 z)
                (existT _ f1_1 f2_2)
                (fiber_component_path_intro
                  (existT _ f1_1 z)
                  (existT _ f1_1 f2_2)
                  (existT _ eq_refl h2))
              = existT _ eq_refl h2
            with
            | eq_refl =>
              match f2_2 with
              | eq_refl => eq_refl
              end
            end
          end
        end f2_2 h2
      end
    end
  end h.

Definition fiber_component_path_unique
  [A B]
  [f : A -> B]
  [y]
  (f1 f2 : fiber f y)
  (h : { p : projT1 f1 = projT1 f2 & transport p (projT2 f1) = projT2 f2 })
: fiber_component_path_intro _ _ (fiber_component_path_elim _ _ h) = h
:=
  match f1
  return
    forall h : {
      p : projT1 f1 = projT1 f2 &
      transport p (projT2 f1) = projT2 f2
    },
    fiber_component_path_intro f1 f2
      (fiber_component_path_elim f1 f2 h) = h
  with
  | existT _ f1_1 f1_2 =>
    match f2
    return
      forall h : {
        p : f1_1 = projT1 f2 &
        transport p f1_2 = projT2 f2
      },
      fiber_component_path_intro (existT _ f1_1 f1_2) f2
        (fiber_component_path_elim (existT _ f1_1 f1_2) f2 h) = h
    with
    | existT _ f2_1 f2_2 =>
      fun h =>
      match h
      return
        fiber_component_path_intro
          (existT _ f1_1 f1_2)
          (existT _ f2_1 f2_2)
          (fiber_component_path_elim
            (existT _ f1_1 f1_2)
            (existT _ f2_1 f2_2)
            h)
        = h
      with
      | existT _ h1 h2 =>
        match h1
        in _ = z
        return
          forall (f2_2 : f z = y) (h2 : transport h1 f1_2 = f2_2),
          fiber_component_path_intro
            (existT _ f1_1 f1_2)
            (existT _ z f2_2)
            (fiber_component_path_elim
              (existT _ f1_1 f1_2)
              (existT _ z f2_2)
              (existT _ h1 h2))
          = existT _ h1 h2
        with
        | eq_refl =>
          match f1_2
          in _ = z
          return
            forall (f2_2 : f f1_1 = z) (h2 : transport eq_refl f1_2 = f2_2),
            fiber_component_path_intro
              (existT _ f1_1 f1_2)
              (existT _ f1_1 f2_2)
              (fiber_component_path_elim
                (existT _ f1_1 f1_2)
                (existT _ f1_1 f2_2)
                (existT _ eq_refl h2))
            = existT _ eq_refl h2
          with
          | eq_refl =>
            fun (f2_2 : f f1_1 = f f1_1) (h2 : eq_refl = f2_2) =>
            match h2 with
            | eq_refl => eq_refl
            end
          end
        end f2_2 h2
      end
    end
  end h.

Theorem fiber_component_path_intro_is_equiv :
  forall A B (f : A -> B) y (f1 f2 : fiber f y),
  IsEquiv (fiber_component_path_intro f1 f2).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  exists (fiber_component_path_elim f1 f2).
  split; intro.
  - apply fiber_component_path_compute.
  - apply fiber_component_path_unique.
Qed.

Theorem fiber_component_path_elim_is_equiv :
  forall A B (f : A -> B) y (f1 f2 : fiber f y),
  IsEquiv (fiber_component_path_elim f1 f2).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  exists (fiber_component_path_intro f1 f2).
  split; intro.
  - apply fiber_component_path_unique.
  - apply fiber_component_path_compute.
Qed.

Definition fiber_path_intro [A B] [f : A -> B] [y] (f1 f2 : fiber f y)
: { p : projT1 f1 = projT1 f2 & concat (ap f p) (projT2 f2) = projT2 f1 } ->
  f1 = f2
:= sigma_path_intro _ _ ∘ fiber_component_path_intro f1 f2.

Definition fiber_path_elim [A B] [f : A -> B] [y] (f1 f2 : fiber f y)
: f1 = f2 ->
  { p : projT1 f1 = projT1 f2 & concat (ap f p) (projT2 f2) = projT2 f1 }
:= fiber_component_path_elim _ _ ∘ @sigma_path_elim _ _ _ _.

Definition fiber_path_compute
  [A B]
  [f : A -> B]
  [y]
  (f1 f2 : fiber f y)
  (h : { p : projT1 f1 = projT1 f2 & concat (ap f p) (projT2 f2) = projT2 f1 })
: fiber_path_elim _ _ (fiber_path_intro _ _ h) = h
:=
  transport
    (P := fun x => fiber_component_path_elim _ _ x = h)
    (inv (sigma_path_compute _ _ (fiber_component_path_intro f1 f2 h)))
    (fiber_component_path_compute _ _ h).

Definition fiber_path_unique
  [A B]
  [f : A -> B]
  [y]
  (f1 f2 : fiber f y)
  (h : f1 = f2)
: fiber_path_intro _ _ (fiber_path_elim _ _ h) = h
:= transport
  (P := fun x => sigma_path_intro f1 f2 x = h)
  (inv (fiber_component_path_unique _ _ (sigma_path_elim h)))
  (inv (sigma_path_unique h)).

Theorem fiber_path_intro_is_equiv :
  forall A B (f : A -> B) y (f1 f2 : fiber f y),
  IsEquiv (fiber_path_intro f1 f2).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  exists (fiber_path_elim f1 f2).
  split; intro.
  - apply fiber_path_compute.
  - apply fiber_path_unique.
Qed.

Theorem fiber_path_elim_is_equiv :
  forall A B (f : A -> B) y (f1 f2 : fiber f y),
  IsEquiv (fiber_path_elim f1 f2).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  exists (fiber_path_intro f1 f2).
  split; intro.
  - apply fiber_path_unique.
  - apply fiber_path_compute.
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
  pose proof fiber_path_elim_is_equiv.
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
  rewrite ap_compose.
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

Definition linv [A B] (f : A -> B) := { g : B -> A & Homotopy (g ∘ f) id }.

Definition rinv [A B] (f : A -> B) := { g : B -> A & Homotopy (f ∘ g) id }.

Theorem precompose_is_equiv :
  forall A B C (f : B -> C), IsEquiv f -> IsEquiv (fun g : A -> B => f ∘ g).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  destruct X.
  do 2 destruct s.
  exists (fun h : A -> C => x ∘ h).
  unfold id, compose in *.
  split; intro.
  - apply pi_path_intro.
    intro.
    rewrite x0.
    reflexivity.
  - apply pi_path_intro.
    intro.
    rewrite x1.
    reflexivity.
Qed.

Theorem postcompose_is_equiv :
  forall A B C (f : A -> B), IsEquiv f -> IsEquiv (fun g : B -> C => g ∘ f).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  destruct X.
  do 2 destruct s.
  exists (fun h : A -> C => h ∘ x).
  unfold id, compose in *.
  split; intro; apply pi_path_intro; intro.
  - rewrite x1.
    reflexivity.
  - rewrite x0.
    reflexivity.
Qed.

Definition to_linv [A B] [f : A -> B] (li : { g : B -> A & g ∘ f = id })
: linv f
:=
  existT
    (fun g : B -> A => Homotopy (g ∘ f) id)
    (projT1 li)
    (pi_path_elim (projT2 li)).

Definition to_rinv [A B] [f : A -> B] (ri : { g : B -> A & f ∘ g = id })
: rinv f
:=
  existT
    (fun g : B -> A => Homotopy (f ∘ g) id)
    (projT1 ri)
    (pi_path_elim (projT2 ri)).

Theorem to_linv_is_equiv : forall A B (f : A -> B), IsEquiv (@to_linv _ _ f).
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
        (pi_path_intro ((projT1 li) ∘ f) id (projT2 li))
  ).
  split; intro.
  - unfold compose, id in *.
    destruct x.
    cbn.
    destruct e.
    rewrite <- pi_path_unique.
    reflexivity.
  - unfold compose, id in *.
    destruct x.
    cbn.
    rewrite (
      pi_path_compute
        (fun x0 : A => x (f x0))
        (fun x0 : A => x0)
    ).
    reflexivity.
Qed.

Theorem to_rinv_is_equiv : forall A B (f : A -> B), IsEquiv (@to_rinv _ _ f).
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
        (pi_path_intro (f ∘ (projT1 li)) id (projT2 li))
  ).
  split; intro.
  - unfold compose, id in *.
    destruct x.
    cbn.
    destruct e.
    rewrite <- pi_path_unique.
    reflexivity.
  - unfold compose, id in *.
    destruct x.
    cbn.
    rewrite (
      pi_path_compute
        (fun x0 : B => f (x x0))
        (fun x0 : B => x0)
    ).
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

(* Being an equivalence is a mere proposition. *)

Definition lcoh [A B] [f : A -> B] (li : linv f) := {
  epsilon : Homotopy (f ∘ projT1 li) id
          & forall y, ap (projT1 li) (epsilon y) = projT2 li (projT1 li y)
}.

Definition rcoh [A B] [f : A -> B] (ri : rinv f) := {
  eta : Homotopy (projT1 ri ∘ f) id
      & forall x, ap f (eta x) = projT2 ri (f x)
}.

Definition lcoh_alternate [A B] [f : A -> B] (li : linv f) := forall y, {
  epsilon : f (projT1 li y) = y
          & ap (projT1 li) epsilon = projT2 li (projT1 li y)
}.

Definition rcoh_alternate [A B] [f : A -> B] (ri : rinv f) := forall x, {
  eta : projT1 ri (f x) = x
      & ap f eta = projT2 ri (f x)
}.

Definition rcoh_to_rcoh_alternate [A B] [f : A -> B] [ri : rinv f]
  (rc : rcoh ri) : rcoh_alternate ri
:= fun x => existT _ (projT1 rc x) (projT2 rc x).

Definition rcoh_alternate_to_rcoh [A B] [f : A -> B] [ri : rinv f]
  (rc : rcoh_alternate ri) : rcoh ri
:= existT _ (fun x => projT1 (rc x)) (fun x => projT2 (rc x)).

Theorem rcoh_to_rcoh_alternate_is_equiv :
  forall A B (f : A -> B) (ri : rinv f),
  IsEquiv (@rcoh_to_rcoh_alternate _ _ _ ri).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  exists (@rcoh_alternate_to_rcoh _ _ _ ri).
  split; intro; unfold
    compose, id, rcoh_to_rcoh_alternate, rcoh_alternate_to_rcoh.
  - destruct x.
    reflexivity.
  - cbn.
    apply pi_path_intro.
    intro.
    rewrite <- sigT_eta.
    reflexivity.
Qed.

Theorem rcoh_alternate_to_rcoh_is_equiv :
  forall A B (f : A -> B) (ri : rinv f),
  IsEquiv (@rcoh_alternate_to_rcoh _ _ _ ri).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  exists (@rcoh_to_rcoh_alternate _ _ _ ri).
  split; intro; unfold
    compose, id, rcoh_to_rcoh_alternate, rcoh_alternate_to_rcoh.
  - cbn.
    apply pi_path_intro.
    intro.
    rewrite <- sigT_eta.
    reflexivity.
  - destruct x.
    reflexivity.
Qed.

Definition lcoh_to_lcoh_alternate [A B] [f : A -> B] [li : linv f]
  (lc : lcoh li) : lcoh_alternate li
:= fun x => existT _ (projT1 lc x) (projT2 lc x).

Definition lcoh_alternate_to_lcoh [A B] [f : A -> B] [li : linv f]
  (lc : lcoh_alternate li) : lcoh li
:= existT _ (fun x => projT1 (lc x)) (fun x => projT2 (lc x)).

Theorem lcoh_to_lcoh_alternate_is_equiv :
  forall A B (f : A -> B) (li : linv f),
  IsEquiv (@lcoh_to_lcoh_alternate _ _ _ li).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  exists (@lcoh_alternate_to_lcoh _ _ _ li).
  split; intro; unfold
    compose, id, lcoh_to_lcoh_alternate, lcoh_alternate_to_lcoh.
  - destruct x.
    reflexivity.
  - cbn.
    apply pi_path_intro.
    intro.
    rewrite <- sigT_eta.
    reflexivity.
Qed.

Theorem lcoh_alternate_to_lcoh_is_equiv :
  forall A B (f : A -> B) (li : linv f),
  IsEquiv (@lcoh_alternate_to_lcoh _ _ _ li).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  exists (@lcoh_to_lcoh_alternate _ _ _ li).
  split; intro; unfold
    compose, id, lcoh_to_lcoh_alternate, lcoh_alternate_to_lcoh.
  - cbn.
    apply pi_path_intro.
    intro.
    rewrite <- sigT_eta.
    reflexivity.
  - destruct x.
    reflexivity.
Qed.

Definition rcoh_alternate_to_fiber
  [A B] [f : A -> B] [ri : rinv f]
  (rc : rcoh_alternate ri)
: forall x1,
    existT (fun x2 => f x2 = f x1)
      (projT1 ri (f x1))
      (projT2 ri (f x1)) =
    existT (fun x2 => f x2 = f x1)
      x1
      eq_refl
:= fun x1 =>
  @fiber_path_intro _ _ f (f x1)
  (
    existT (fun x2 => f x2 = f x1)
      (projT1 ri (f x1))
      (projT2 ri (f x1))
  ) (
    existT (fun x2 => f x2 = f x1)
      x1
      eq_refl
  ) (existT _ (projT1 (rc x1)) (projT2 (rc x1))).

Definition fiber_to_rcoh_alternate
  [A B]
  [f : A -> B]
  (ri : rinv f)
  (h :
    forall x1,
      existT (fun x2 => f x2 = f x1)
        (projT1 ri (f x1))
        (projT2 ri (f x1)) =
      existT (fun x2 => f x2 = f x1)
        x1
        eq_refl
  ) : rcoh_alternate ri
:= fun x1 =>
  existT _
    (projT1 (fiber_path_elim _ _ (h x1)))
    (projT2 (fiber_path_elim _ _ (h x1))).

Theorem rcoh_alternate_to_fiber_is_equiv :
  forall A B (f : A -> B) (ri : rinv f),
  IsEquiv (@rcoh_alternate_to_fiber _ _ _ ri).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  exists (@fiber_to_rcoh_alternate _ _ _ ri).
  split; intro; unfold
    compose, id, rcoh_alternate_to_fiber, fiber_to_rcoh_alternate.
  - apply pi_path_intro.
    intro.
    rewrite <- sigT_eta.
    rewrite fiber_path_compute.
    rewrite <- sigT_eta.
    reflexivity.
  - apply pi_path_intro.
    intro.
    rewrite <- sigT_eta.
    rewrite <- sigT_eta.
    rewrite fiber_path_unique.
    reflexivity.
Qed.

Theorem fiber_to_rcoh_alternate_is_equiv :
  forall A B (f : A -> B) (ri : rinv f),
  IsEquiv (@fiber_to_rcoh_alternate _ _ _ ri).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  exists (@rcoh_alternate_to_fiber _ _ _ ri).
  split; intro; unfold
    compose, id, rcoh_alternate_to_fiber, fiber_to_rcoh_alternate.
  - apply pi_path_intro.
    intro.
    rewrite <- sigT_eta.
    rewrite <- sigT_eta.
    rewrite fiber_path_unique.
    reflexivity.
  - apply pi_path_intro.
    intro.
    rewrite <- sigT_eta.
    rewrite fiber_path_compute.
    rewrite <- sigT_eta.
    reflexivity.
Qed.

Definition lcoh_alternate_to_fiber [A B] [f : A -> B] [li : linv f]
  (lc : lcoh_alternate li)
: forall y1,
    existT (fun y2 => projT1 li y2 = projT1 li y1)
      (f (projT1 li y1))
      (projT2 li (projT1 li y1)) =
    existT (fun y2 => projT1 li y2 = projT1 li y1)
      y1
      eq_refl
:=
  fun y1 =>
    @fiber_path_intro _ _ (projT1 li) (projT1 li y1)
      (
        existT (fun y2 => projT1 li y2 = projT1 li y1)
          (f (projT1 li y1))
          (projT2 li (projT1 li y1))
      ) (
        existT (fun y2 => projT1 li y2 = projT1 li y1)
          y1
          eq_refl
      ) (existT _ (projT1 (lc y1)) (projT2 (lc y1))).

Definition fiber_to_lcoh_alternate [A B] [f : A -> B]
  (li : linv f)
  (h :
    forall y1,
      existT (fun y2 => projT1 li y2 = projT1 li y1)
        (f (projT1 li y1))
        (projT2 li (projT1 li y1)) =
      existT (fun y2 => projT1 li y2 = projT1 li y1)
        y1
        eq_refl
  ) : lcoh_alternate li
:= fun x1 =>
  existT _
    (projT1 (fiber_path_elim _ _ (h x1)))
    (projT2 (fiber_path_elim _ _ (h x1))).

Theorem lcoh_alternate_to_fiber_is_equiv :
  forall A B (f : A -> B) (li : linv f),
  IsEquiv (@lcoh_alternate_to_fiber _ _ _ li).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  exists (@fiber_to_lcoh_alternate _ _ _ li).
  split; intro; unfold
    compose, id, lcoh_alternate_to_fiber, fiber_to_lcoh_alternate.
  - apply pi_path_intro.
    intro.
    rewrite <- sigT_eta.
    rewrite fiber_path_compute.
    rewrite <- sigT_eta.
    reflexivity.
  - apply pi_path_intro.
    intro.
    rewrite <- sigT_eta.
    rewrite <- sigT_eta.
    rewrite fiber_path_unique.
    reflexivity.
Qed.

Theorem fiber_to_lcoh_alternate_is_equiv :
  forall A B (f : A -> B) (li : linv f),
  IsEquiv (@fiber_to_lcoh_alternate _ _ _ li).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  exists (@lcoh_alternate_to_fiber _ _ _ li).
  split; intro; unfold
    compose, id, lcoh_alternate_to_fiber, fiber_to_lcoh_alternate.
  - apply pi_path_intro.
    intro.
    rewrite <- sigT_eta.
    rewrite <- sigT_eta.
    rewrite fiber_path_unique.
    reflexivity.
  - apply pi_path_intro.
    intro.
    rewrite <- sigT_eta.
    rewrite fiber_path_compute.
    rewrite <- sigT_eta.
    reflexivity.
Qed.

Definition rcoh_to_fiber [A B] [f : A -> B] [ri : rinv f]
: rcoh ri ->
  forall x1,
    existT (fun x2 => f x2 = f x1) (projT1 ri (f x1)) (projT2 ri (f x1)) =
    existT (fun x2 => f x2 = f x1) x1 eq_refl
:= @rcoh_alternate_to_fiber _ _ _ ri ∘ @rcoh_to_rcoh_alternate _ _ _ ri.

Definition fiber_to_rcoh [A B] [f : A -> B] [ri : rinv f]
: (forall x1,
    existT (fun x2 => f x2 = f x1) (projT1 ri (f x1)) (projT2 ri (f x1)) =
    existT (fun x2 => f x2 = f x1) x1 eq_refl) ->
  rcoh ri
:= @rcoh_alternate_to_rcoh _ _ _ ri ∘ fiber_to_rcoh_alternate ri.

Theorem rcoh_to_fiber_is_equiv :
  forall A B (f : A -> B) (ri : rinv f), IsEquiv (@rcoh_to_fiber _ _ _ ri).
Proof.
  intros.
  apply comp_is_equiv.
  - apply rcoh_to_rcoh_alternate_is_equiv.
  - apply rcoh_alternate_to_fiber_is_equiv.
Qed.

Theorem fiber_to_rcoh_is_equiv :
  forall A B (f : A -> B) (ri : rinv f), IsEquiv (@fiber_to_rcoh _ _ _ ri).
Proof.
  intros.
  apply comp_is_equiv.
  - apply fiber_to_rcoh_alternate_is_equiv.
  - apply rcoh_alternate_to_rcoh_is_equiv.
Qed.

Definition lcoh_to_fiber [A B] [f : A -> B] [li : linv f]
: lcoh li ->
  forall y1,
    existT (fun y2 => projT1 li y2 = projT1 li y1)
      (f (projT1 li y1))
      (projT2 li (projT1 li y1)) =
    existT (fun y2 => projT1 li y2 = projT1 li y1)
      y1
      eq_refl
:= @lcoh_alternate_to_fiber _ _ _ li ∘ @lcoh_to_lcoh_alternate _ _ _ li.

Definition fiber_to_lcoh [A B] [f : A -> B] (li : linv f)
: (forall y1,
    existT (fun y2 => projT1 li y2 = projT1 li y1)
      (f (projT1 li y1))
      (projT2 li (projT1 li y1)) =
    existT (fun y2 => projT1 li y2 = projT1 li y1)
      y1
      eq_refl) ->
  lcoh li
:= @lcoh_alternate_to_lcoh _ _ _ li ∘ fiber_to_lcoh_alternate li.

Theorem lcoh_to_fiber_is_equiv :
  forall A B (f : A -> B) (li : linv f), IsEquiv (@lcoh_to_fiber _ _ _ li).
Proof.
  intros.
  apply comp_is_equiv.
  - apply lcoh_to_lcoh_alternate_is_equiv.
  - apply lcoh_alternate_to_fiber_is_equiv.
Qed.

Theorem fiber_to_lcoh_is_equiv :
  forall A B (f : A -> B) (li : linv f), IsEquiv (@fiber_to_lcoh _ _ _ li).
Proof.
  intros.
  apply comp_is_equiv.
  - apply fiber_to_lcoh_alternate_is_equiv.
  - apply lcoh_alternate_to_lcoh_is_equiv.
Qed.

Theorem lcoh_is_contr :
  forall A B (f : A -> B) (li : linv f), IsEquiv f -> IsContr (lcoh li).
Proof.
  intros.
  apply equiv_trunc with (f := @fiber_to_lcoh _ _ _ li).
  - apply fiber_to_lcoh_is_equiv.
  - assert (
      forall y1 : B, IsContr (
        existT (fun y2 : B => projT1 li y2 = projT1 li y1)
          (f (projT1 li y1)) (projT2 li (projT1 li y1)) =
        existT (fun y2 : B => projT1 li y2 = projT1 li y1) y1 eq_refl
      )
    ).
    + intro.
      assert (IsEquiv (projT1 li)).
      * pose proof (linv_is_contr _ _ f X).
        destruct X0.
        apply quasi_inv_is_equiv.
        unfold QuasiInv.
        destruct X, s, s.
        pose proof (e (existT _ x0 x1)).
        pose proof (e li).
        subst x.
        exists f.
        destruct li.
        cbn in *.
        destruct (sigma_path_elim H0).
        cbn in *.
        subst x0.
        split; assumption.
      * pose proof (fiber_is_contr _ _ (projT1 li) (projT1 li y1) X0).
        pose proof (
          is_trunc_cumulative 0 (fiber (projT1 li) (projT1 li y1)) X1
        ).
        clear X0 X1.
        cbn in *.
        specialize (
          H
            (
              existT (fun y2 : B => projT1 li y2 = projT1 li y1)
                (f (projT1 li y1))
                (projT2 li (projT1 li y1))
            )
            (
              existT (fun y2 : B => projT1 li y2 = projT1 li y1)
                y1
                eq_refl
            )
        ).
        destruct H.
        exists x.
        exact e.
    + exists (fun y1 => projT1 (X0 y1)).
      intros.
      apply pi_path_intro.
      intro.
      pose proof (X0 x0).
      destruct X1.
      rewrite <- (e (x x0)).
      rewrite <- (e (projT1 (X0 x0))).
      reflexivity.
(*
  At this point, all goals have been discharged. `Qed` succeeds interactively,
  but batch compilation fails in Rocq 9.0.1 with this error:

  ```
  Error:
  Anomaly
  "File "kernel/constant_typing.ml", line 272, characters 7-13:
    Assertion failed."
  Please report at http://rocq-prover.org/bugs/.
  ```

  So, for now, we abandon this proof. Fortunately, nothing below depend on it.
*)
Abort.

Theorem rcoh_is_contr :
  forall A B (f : A -> B) (ri : rinv f), IsEquiv f -> IsContr (rcoh ri).
Proof.
  intros.
  apply equiv_trunc with (f := @fiber_to_rcoh _ _ _ ri).
  - apply fiber_to_rcoh_is_equiv.
  - assert (
      forall x1 : A, IsContr (
        existT (fun x2 : A => f x2 = f x1)
          (projT1 ri (f x1)) (projT2 ri (f x1)) =
        existT (fun x2 : A => f x2 = f x1) x1 eq_refl
      )
    ).
    + intro.
      pose proof (fiber_is_contr _ _ f (f x1) X).
      pose proof (is_trunc_cumulative 0 (fiber f (f x1)) X0).
      clear X0.
      cbn in *.
      specialize (
        H
          (
            existT (fun x2 : A => f x2 = f x1)
            (projT1 ri (f x1))
            (projT2 ri (f x1))
          )
          (
            existT (fun x2 : A => f x2 = f x1)
            x1
            eq_refl
          )
      ).
      destruct H.
      exists x.
      exact e.
    + exists (fun x1 => projT1 (X0 x1)).
      intros.
      apply pi_path_intro.
      intro.
      pose proof (X0 x0).
      destruct X1.
      rewrite <- (e (x x0)).
      rewrite <- (e (projT1 (X0 x0))).
      reflexivity.
Qed.

Definition is_equiv_to_rinv_rcoh [A B] [f : A -> B]
  (e : IsEquiv f) : { ri : rinv f & rcoh ri }
:=
  existT _
    (existT _ (projT1 e) (projT1 (projT2 (projT2 e))))
    (existT _ (projT1 (projT2 e)) (projT2 (projT2 (projT2 e)))).

Definition rinv_rcoh_to_is_equiv [A B] (f : A -> B)
  (e : { ri : rinv f & rcoh ri }) : IsEquiv f
:=
  existT _
    (projT1 (projT1 e))
    (
      existT _
        (projT1 (projT2 e))
        (existT _ (projT2 (projT1 e)) (projT2 (projT2 e)))
    ).

Theorem is_equiv_to_rinv_rcoh_is_equiv :
  forall A B (f : A -> B), IsEquiv (@is_equiv_to_rinv_rcoh _ _ f).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  exists (@rinv_rcoh_to_is_equiv _ _ f).
  split; intro; unfold compose, id.
  - destruct x, s, s.
    reflexivity.
  - destruct x, x, r.
    reflexivity.
Qed.

Theorem is_equiv_rinv_rcoh_to_is_equiv :
  forall A B (f : A -> B), IsEquiv (@rinv_rcoh_to_is_equiv _ _ f).
Proof.
  intros.
  apply quasi_inv_is_equiv.
  unfold QuasiInv.
  exists (@is_equiv_to_rinv_rcoh _ _ f).
  split; intro; unfold compose, id.
  - destruct x, x, r.
    reflexivity.
  - destruct x, s, s.
    reflexivity.
Qed.

Theorem is_equiv_is_prop : forall A B (f : A -> B), IsProp (IsEquiv f).
Proof.
  intros.
  apply equiv_trunc with (f := @rinv_rcoh_to_is_equiv _ _ f).
  - apply is_equiv_rinv_rcoh_to_is_equiv.
  - apply proof_irrelevance_is_prop.
    intros.
    apply sigma_path_intro.
    assert (projT1 x = projT1 y).
    + pose proof (rinv_is_contr _ _ f (rinv_rcoh_to_is_equiv _ x)).
      destruct X.
      rewrite <- (e (projT1 x)).
      rewrite <- (e (projT1 y)).
      reflexivity.
    + destruct x, y.
      cbn in *.
      subst x.
      exists eq_refl.
      cbn.
      pose proof (
        rcoh_is_contr _ _ f x0 (rinv_rcoh_to_is_equiv _ (existT _ x0 r))
      ).
      destruct H.
      rewrite <- (e r).
      rewrite <- (e r0).
      reflexivity.
Qed.

(*
  Now that we know that being an equivalence is a mere proposition, we can
  prove more about equalities in the universe.
*)

Theorem type_path_refl : forall A, eq_refl = type_path_intro (id_is_equiv A).
Proof.
  intro.
  apply type_path_unique.
Qed.

Theorem type_path_inv :
  forall A B (p : A = B),
  inv p = type_path_intro (inv_is_equiv _ _ _ (projT2 (type_path_elim p))).
Proof.
  intros.
  destruct p.
  change (projT1 (type_path_elim eq_refl)) with (@id A).
  replace (projT2 (type_path_elim eq_refl)) with (
    existT
      (
        fun g : A -> A =>
          {eta : Homotopy (g ∘ id) id &
          {epsilon : Homotopy (id ∘ g) id &
          forall x : A, ap id (eta x) = epsilon (id x)}}
      )
      (@id A)
      (
        existT
          _
          (fun _ => eq_refl)
          (existT _ (fun _ => eq_refl) (fun _ => eq_refl))
      )
  ).
  + cbn.
    rewrite type_path_refl.
    f_equal.
    apply is_equiv_is_prop.
  + apply is_equiv_is_prop.
Qed.

Theorem type_path_compose :
  forall A B C (p : A = B) (q : B = C),
  concat p q =
  type_path_intro (
    comp_is_equiv _ _ _ _ _
      (projT2 (type_path_elim p))
      (projT2 (type_path_elim q))
  ).
Proof.
  intros.
  destruct p, q.
  change (projT1 (type_path_elim eq_refl)) with (@id A).
  cbn.
  rewrite type_path_refl.
  f_equal.
  apply is_equiv_is_prop.
Qed.

(* An example of using homotopy type theory *)

Inductive Bit : U :=
| Zero
| One.

Inductive Weekend : U :=
| Saturday
| Sunday.

Definition bit_to_weekend x :=
  match x with
  | Zero => Saturday
  | One => Sunday
  end.

Definition weekend_to_bit x :=
  match x with
  | Saturday => Zero
  | Sunday => One
  end.

Theorem bit_weekend_equiv : IsEquiv bit_to_weekend.
Proof.
  apply quasi_inv_is_equiv.
  exists weekend_to_bit.
  split; intro; destruct x; reflexivity.
Qed.

Definition bit_weekend_path : Bit = Weekend :=
  type_path_intro bit_weekend_equiv.

Theorem transport_bit :
  transport (P := @id U) bit_weekend_path = bit_to_weekend.
Proof.
  rewrite type_transport.
  rewrite ap_id.
  unfold bit_weekend_path.
  rewrite type_path_compute.
  reflexivity.
Qed.

Theorem transport_weekend :
  transport (P := @id U) (inv bit_weekend_path) = weekend_to_bit.
Proof.
  rewrite type_transport.
  rewrite ap_id.
  unfold bit_weekend_path.
  rewrite type_path_inv.
  repeat rewrite type_path_compute.
  cbn.
  apply function_path_intro.
  intro.
  destruct bit_weekend_equiv.
  destruct s, s.
  cbn.
  unfold Homotopy, compose, id in *.
  rewrite <- (x2 x).
  rewrite x1.
  destruct (x0 x); reflexivity.
Qed.

Theorem transport_bits :
  transport (P := fun T : U => pair T T) bit_weekend_path
    (existT _ Zero One) =
  existT _ Saturday Sunday.
Proof.
  rewrite pair_transport.
  cbn.
  change (fun x : U => x) with (@id U).
  rewrite transport_bit.
  reflexivity.
Qed.

Theorem transport_weekends :
  transport (P := fun T : U => pair T T) (inv bit_weekend_path)
    (existT _ Saturday Sunday) =
  (existT _ Zero One).
Proof.
  rewrite pair_transport.
  cbn.
  change (fun x : U => x) with (@id U).
  rewrite transport_weekend.
  reflexivity.
Qed.

Definition invert_bit x :=
  match x with
  | Zero => One
  | One => Zero
  end.

Definition invert_weekend x :=
  match x with
  | Saturday => Sunday
  | Sunday => Saturday
  end.

Theorem transport_invert_bit :
  transport (P := fun T : U => T -> T) bit_weekend_path
    invert_bit =
  invert_weekend.
Proof.
  rewrite function_transport.
  change (fun x : U => x) with (@id U).
  rewrite transport_bit, transport_weekend.
  apply function_path_intro.
  intro.
  destruct x; reflexivity.
Qed.

Theorem transport_invert_weekend :
  transport (P := fun T : U => T -> T) (inv bit_weekend_path)
    invert_weekend =
  invert_bit.
Proof.
  rewrite function_transport.
  change (fun x : U => x) with (@id U).
  rewrite inv_inv.
  rewrite transport_bit, transport_weekend.
  apply function_path_intro.
  intro.
  destruct x; reflexivity.
Qed.

Theorem invert_bit_involution :
  forall x, invert_bit (invert_bit x) = x.
Proof.
  destruct x; reflexivity.
Qed.

Theorem invert_weekend_involution :
  forall x, invert_weekend (invert_weekend x) = x.
Proof.
  intros.
  rewrite <- transport_invert_bit.
  repeat rewrite function_transport.
  rewrite transport_concat.
  rewrite right_inv.
  rewrite transport_refl.
  rewrite invert_bit_involution.
  rewrite transport_concat.
  rewrite left_inv.
  rewrite transport_refl.
  reflexivity.
Qed.

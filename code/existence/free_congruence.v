(**
Here we define the freely generated congruence relation.
 *)
Require Import prelude.all.

Require Import setoids.base.
Require Import setoids.setoid_category.

Require Import syntax.hit_signature.
Require Import algebras.set_algebra.
Require Import algebras.setoid_algebra.
Require Import algebras.univalent_algebra.

(**
First we say how to construct congruence relations.
The congruence relation is generated by `R`, and the resulting setoid should have a lift of `f`.
We generate this relation simultaneously with each polynomial lift of it.
 *)
Inductive generated_rel
          {X : hSet}
          (R : X → X → UU)
  : ∏ (P Q : poly_code)
      (f : ⦃ Q ⦄ X → X),
    ⦃ P ⦄ X → ⦃ P ⦄ X → UU
  := 
  | refl : ∏ {P Q : poly_code}
             (f : ⦃ Q ⦄ X → X)
             (x : ⦃ P ⦄ X),
           generated_rel R P Q f x x
  | sym : ∏ {P Q : poly_code}
            (f : ⦃ Q ⦄ X → X)
            {x y : ⦃ P ⦄ X},
          generated_rel R P Q f x y
          → generated_rel R P Q f y x
  | trans : ∏ {P Q : poly_code}
              (f : ⦃ Q ⦄ X → X)
              {x y z : ⦃ P ⦄ X},
            generated_rel R P Q f x y
            → generated_rel R P Q f y z
            → generated_rel R P Q f x z
  | pair_path : ∏ {P₁ P₂ Q : poly_code}
                  (f : ⦃ Q ⦄ X → X)
                  {x₁ x₂ : ⦃ P₁ ⦄ X}
                  {y₁ y₂ : ⦃ P₂ ⦄ X},
                generated_rel R P₁ Q f x₁ x₂
                → generated_rel R P₂ Q f y₁ y₂
                → generated_rel R (P₁ * P₂) Q f (x₁ ,, y₁) (x₂ ,, y₂)
  | inl_path : ∏ {P₁ P₂ Q : poly_code}
                 (f : ⦃ Q ⦄ X → X)
                 {x₁ x₂ : ⦃ P₁ ⦄ X},
               generated_rel R P₁ Q f x₁ x₂
               → generated_rel R (P₁ + P₂) Q f (inl x₁) (inl x₂)
  | inr_path : ∏ {P₁ P₂ Q : poly_code}
                 (f : ⦃ Q ⦄ X → X)
                 {y₁ y₂ : ⦃ P₂ ⦄ X},
               generated_rel R P₂ Q f y₁ y₂
               → generated_rel R (P₁ + P₂) Q f (inr y₁) (inr y₂)
  | path : ∏ {Q : poly_code}
             (f : ⦃ Q ⦄ X → X)
             {x y : X},
           R x y → generated_rel R I Q f x y
  | cong : ∏ {Q : poly_code}
             (f : ⦃ Q ⦄ X → X)
             {x y : ⦃ Q ⦄ X},
           generated_rel R Q Q f x y
           → generated_rel R I Q f (f x) (f y).

(**
A mapping principle for the generated equivalence relation.
 *)
Definition map_generated_rel
           {P Q : poly_code}
           (X : hSet)
           (f : ⦃ Q ⦄ X → X)
           (R : X → X → UU)
           (Y : setoid_prealgebras Q)
           (g : X → pr1 Y : setoid)  
           {x y : ⦃ P ⦄ X}
           (q : ∏ z, g(f z) ≡ pr1 (pr2 Y) (#⦃ Q ⦄ g z))
           (HY : ∏ (x y : X), R x y → g x ≡ g y)
           (p : generated_rel R P Q f x y)
  : poly_eq_rel P (pr1 Y : setoid) (#⦃ P ⦄ g x) (#⦃ P ⦄ g y).
Proof.
  induction p ; simpl.
  - apply (id _)%setoid.
  - refine (! _)%setoid.
    apply IHp ; assumption.
  - refine (IHp1 _ _ _ _ @ IHp2 _ _ _ _)%setoid ; assumption.
  - split.
    + apply IHp1 ; assumption.
    + apply IHp2 ; assumption.
  - apply IHp ; assumption.
  - apply IHp ; assumption.
  - apply HY ; assumption.
  - specialize (IHp Y g q HY).
    refine (q x @ map_eq _ _ @ !(q y))%setoid.
    exact IHp.
Qed.

(**
This relation gives rise to an equivalence relation.
Note that we use the propositional truncation here to guarantee it's a proposition.
 *)
Definition generated_eqrel
           (X : hSet)
           {Q : poly_code}
           (f : ⦃ Q ⦄ X → X)
           (R : X → X → UU)
  : eqrel X.
Proof.
  use make_eq_rel.
  - intros x y.
    exact (∥ generated_rel R I Q f x y ∥).
  - intro.
    apply hinhpr.
    apply refl.
  - intros x y.
    use factor_through_squash.
    + apply ishinh.
    + intro p.
      apply hinhpr.
      apply sym.
      exact p.
  - intros x y z.
    use factor_through_squash.
    + apply impred.
      intro.
      apply ishinh.
    + intro p.
      use factor_through_squash.
      * apply ishinh.
      * intro q.
        apply hinhpr.
        exact (trans R f p q).
Defined.

(**
We thus get a setoid.
 *)
Definition generated_setoid
           (X : hSet)
           {Q : poly_code}
           (f : ⦃ Q ⦄ X → X)
           (R : X → X → UU)
  : setoid
  := make_setoid (generated_eqrel X f R).

(**
Next we show that we can lift `f`. For this, we need a lemma.
 *)
Definition cong_rel
           (X : hSet)
           (P : poly_code)
           {Q : poly_code}
           (f : ⦃ Q ⦄ X → X)
           (R : X → X → UU)
           (x y : (⟨ P ⟩ (generated_setoid X f R) : setoid))
           (p : x ≡ y)
  : ∥ generated_rel R P Q f x y ∥.
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply hinhpr.
    rewrite p.
    apply refl.
  - revert p.
    cbn in *.
    use factor_through_squash.
    + apply ishinh.
    + intro p.
      apply hinhpr.
      exact p.
  - induction x as [x | x], y as [y | y].
    + specialize (IHP₁ x y p).
      refine (factor_through_squash _ _ IHP₁).
      { apply ishinh. }
      clear IHP₁. clear IHP₂.
      intro IHP₁.
      apply hinhpr.
      apply inl_path.
      exact IHP₁.
    + exact (fromempty p).
    + exact (fromempty p).
    + specialize (IHP₂ x y p).
      refine (factor_through_squash _ _ IHP₂).
      { apply ishinh. }
      clear IHP₁. clear IHP₂.
      intro IHP₂.
      apply hinhpr.
      apply inr_path.
      exact IHP₂.
  - specialize (IHP₁ (pr1 x) (pr1 y) (pr1 p)).
    specialize (IHP₂ (pr2 x) (pr2 y) (pr2 p)).
    refine (factor_through_squash _ _ IHP₁).
    { apply ishinh. }
    clear IHP₁. intro IHP₁.
    refine (factor_through_squash _ _ IHP₂).
    { apply ishinh. }
    clear IHP₂. intro IHP₂.
    apply hinhpr.
    apply pair_path.
    + exact IHP₁.
    + exact IHP₂.
Qed.

(**
This is the lift of `f` to the setoid level
 *)
Definition generated_map
           (X : hSet)
           {Q : poly_code}
           (f : ⦃ Q ⦄ X → X)
           (R : X → X → UU)
  : setoid_morphism
      (⟨ Q ⟩ (generated_setoid X f R))
      (generated_setoid X f R).
Proof.
  use make_setoid_morphism.
  - exact (λ x, f x).
  - intros x y p.
    refine (factor_through_squash _ _ (cong_rel X Q f R x y p)).
    + apply ishinh.
    + intros q.
      apply hinhpr.
      apply cong.
      exact q.
Defined.

(**
The next step is to the relation generated by the path constructors of the HIT.
We use an inductive relation for this.
 *)
Inductive rel
          (Σ : hit_signature)
          (X : hSet)
          (f : ⦃ point_arg Σ ⦄ X → X)
  : X → X → UU
  :=
| path_constr : ∏ (j : path_index Σ)
                  (x : ⦃ path_arg Σ j ⦄ X),
                rel Σ X f
                    (pr1 (set_endpoint (path_lhs Σ j)) (X ,, f) x)
                    (pr1 (set_endpoint (path_rhs Σ j)) (X ,, f) x).

(**
All in all, given a prealgebra (set) on the HIT signature, we get an actual algebra (setoid) of the HIT.
 *)
Section GeneratedAlgebra.
  Context {Σ : hit_signature}.
  Variable (Xalg : set_prealgebras (point_arg Σ)).

  Local Notation X := (prealg_carrier Xalg : hSet).
  Local Notation f := (prealg_operation Xalg : ⦃ point_arg Σ ⦄ X → X).

  Definition mod_congruence
    : setoid_algebra Σ.
  Proof.
    simple refine ((_ ,, _) ,, _).
    - exact (generated_setoid X f (rel Σ X f)).
    - exact (generated_map X f (rel Σ X f)).
    - intros j x.
      apply hinhpr.
      apply path.
      exact (path_constr Σ X f j x).
  Defined.
End GeneratedAlgebra.

(**
Let `Xalg` be a set prealgebra.
The mapping principle on `mod_congruence` says that whenever we have a prealgebra from `Xalg` to the carrier of some setoid algebra `Y`, then we can lift it to `mod_congruence X`.
 *)
Section MapModCongruence.
  Context {Σ : hit_signature}
          {Xalg : set_prealgebras (point_arg Σ)}
          {Y : setoid_algebra Σ}.

  Local Notation X := (prealg_carrier Xalg : hSet).
  Local Notation f := (prealg_operation Xalg : ⦃ point_arg Σ ⦄ X → X).

  Variable (g : Xalg --> setoid_prealgebra_to_set_prealgebra _ (pr1 Y)).

  Local Definition pr1_g_is_setoid_morp
        (x y : alg_carrier (mod_congruence Xalg))
    : x ≡ y → pr1 g x ≡ pr1 g y.
  Proof.
    use factor_through_squash.
    { apply isaprop_setoid_eq. }
    use map_generated_rel.
    - intros z.
      exact (setoid_path (eqtohomot (pr2 g) z)).
    - intros z₁ z₂ r.
      induction r as [j z].
      pose (pr2 Y j (#⦃ path_arg Σ j⦄ (pr1 g) z)).
      simpl in h.
      refine (_ @ h @ _)%setoid.
      + exact (setoid_path (eqtohomot (!(pr2 (set_endpoint (path_lhs Σ j)) _ _ g)) z)).
      + exact (setoid_path (eqtohomot (pr2 (set_endpoint (path_rhs Σ j)) _ _ g) z)).
  Qed.

  Definition map_mod_congruence
    : mod_congruence Xalg --> Y.
  Proof.
    use make_algebra_map.
    - use make_setoid_morphism.
      + exact (pr1 g).
      + exact pr1_g_is_setoid_morp.
    - exact (eqtohomot (pr2 g)).
  Defined.
End MapModCongruence.
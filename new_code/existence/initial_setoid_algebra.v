(**
Here we define the initial setoid algebra.
The carrier of this setoid is the initial prealgebra of the point constructor.
The equivalence relation is the freely generated congruence relation.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.limits.initial.

Require Import prelude.
Require Import setoids.base.
Require Import setoids.setoid_category.
Require Import syntax.containers.
Require Import syntax.hit_signature.
Require Import syntax.W_types.
Require Import algebra.setoid_algebra.
Require Import algebra.set_algebra.


Definition TODO {A : Type} : A.
Admitted.

Local Open Scope container_scope.

Section InitialSetoidAlgebra.
  Variable (Σ : hit_signature).

  Definition initial_setoid_carrier_set
    : hSet
    := W_hSet (point_constr Σ) emptyset.

  Definition initial_setoid_carrier_set_sup
    : ⟦ point_constr Σ ⟧ initial_setoid_carrier_set
      →
      initial_setoid_carrier_set.
  Proof.
    simpl.
    exact (λ x, sup (pr1 x) (pr2 x)).
  Defined.

  Inductive initial_setoid_carrier_rel
    : initial_setoid_carrier_set
      → initial_setoid_carrier_set
      → UU
    :=
  | in_refl : ∏ (x : initial_setoid_carrier_set),
              initial_setoid_carrier_rel x x
  | in_symm : ∏ (x y : initial_setoid_carrier_set),
              initial_setoid_carrier_rel x y
              →
              initial_setoid_carrier_rel y x
  | in_trans : ∏ (x y z : initial_setoid_carrier_set),
               initial_setoid_carrier_rel x y
               →
               initial_setoid_carrier_rel y z
               →
               initial_setoid_carrier_rel x z
  | on_path : ∏ (s : shapes (point_constr Σ))
                (p₁ p₂ : positions (point_constr Σ) s → W (point_constr Σ) emptyset)
                (q : ∏ (x : positions (point_constr Σ) s),
                     initial_setoid_carrier_rel (p₁ x) (p₂ x)),
              initial_setoid_carrier_rel (sup s p₁) (sup s p₂)
  | path_constr : ∏ (i : path_index Σ)
                    (p : path_arg Σ i → initial_setoid_carrier_set),
                  initial_setoid_carrier_rel
                    (sem_endpoint
                       initial_setoid_carrier_set_sup
                       i p
                       (path_lhs Σ i))
                    (sem_endpoint
                       initial_setoid_carrier_set_sup
                       i p
                       (path_rhs Σ i)).
  
  Definition initial_setoid_carrier_hrel
    : hrel initial_setoid_carrier_set.
  Proof.
    intros x y.
    use ishinh.
    exact (initial_setoid_carrier_rel x y).
  Defined.

  Definition initial_setoid_carrier_hrel_istrans
    : istrans initial_setoid_carrier_hrel.
  Proof.
    intros x y z.
    intros p q.
    use (hinhuniv _ p).
    clear p ; intro p.
    use (hinhuniv _ q).
    clear q ; intro q.
    apply hinhpr.
    exact (in_trans _ _ _ p q).
  Qed.

  Definition initial_setoid_carrier_hrel_isrefl
    : isrefl initial_setoid_carrier_hrel.
  Proof.
    intros x.
    apply hinhpr.
    exact (in_refl x).
  Qed.

  Definition initial_setoid_carrier_hrel_issymm
    : issymm initial_setoid_carrier_hrel.
  Proof.
    intros x y.
    intros p.
    use (hinhuniv _ p).
    clear p ; intro p.
    apply hinhpr.
    exact (in_symm _ _ p).
  Qed.
  
  Definition initial_setoid_carrier_eqrel
    : eqrel initial_setoid_carrier_set.
  Proof.
    use make_eqrel.
    - exact initial_setoid_carrier_hrel.
    - repeat split.
      + exact initial_setoid_carrier_hrel_istrans.
      + exact initial_setoid_carrier_hrel_isrefl.
      + exact initial_setoid_carrier_hrel_issymm.
  Defined.

  Definition initial_setoid_carrier
    : setoid.
  Proof.
    use make_setoid.
    - exact initial_setoid_carrier_set.
    - exact initial_setoid_carrier_eqrel.
  Defined.

  Definition initial_setoid_constructor_carrier
    : ⦃ point_constr Σ ⦄ initial_setoid_carrier
      →
      initial_setoid_carrier.
  Proof.
    simpl.
    exact (λ x, sup (pr1 x) (pr2 x)).
  Defined.

  Definition initial_setoid_constructor_on_eq
             {x₁ x₂ : ⦃ point_constr Σ ⦄ initial_setoid_carrier}
             (p : x₁ ≡ x₂)
    : initial_setoid_constructor_carrier x₁
      ≡
      initial_setoid_constructor_carrier x₂.
  Proof.
    induction x₁ as [x₁ y₁].
    induction x₂ as [x₂ y₂].
    induction p as [p q].
    simpl in *.
    induction p.
    cbn in *.
    assert (ishinh
              (∏ (z : positions (point_constr Σ) x₁),
               initial_setoid_carrier_rel (y₁ z) (y₂ z)))
      as X.
    {
      apply TODO.
      (* equivalent to AC, here we might need finiteness *)
    }
    revert X.
    use factor_through_squash.
    - apply ishinh.
    - intro X.
      apply hinhpr.
      apply on_path.
      exact X.
  Qed.

  Definition initial_setoid_constructor
    : setoid_morphism
        (⦃ point_constr Σ ⦄ initial_setoid_carrier)
        initial_setoid_carrier.
  Proof.
    use make_setoid_morphism.
    - exact initial_setoid_constructor_carrier.
    - exact @initial_setoid_constructor_on_eq.
  Defined.

  Definition initial_setoid_prealgebra
    : hit_setoid_prealgebra Σ.
  Proof.
    use make_hit_setoid_prealgebra.
    - exact initial_setoid_carrier.
    - exact initial_setoid_constructor.
  Defined.

  Definition initial_setoid_is_algebra
    : is_hit_setoid_algebra initial_setoid_prealgebra.
  Proof.
    exact (λ i p, hinhpr (path_constr i p)).
  Qed.
  
  Definition initial_setoid_algebra
    : hit_setoid_algebra Σ.
  Proof.
    simple refine (_ ,, _) ; simpl.
    - exact initial_setoid_prealgebra.
    - exact initial_setoid_is_algebra.
  Defined.

  Definition initial_setoid_algebra_uniqueness
             (Y : hit_setoid_algebra Σ)
    : isaprop (hit_setoid_algebra Σ ⟦ initial_setoid_algebra, Y ⟧).
  Proof.
    use invproofirrelevance.
    intros φ₁ φ₂.
    use subtypePath.
    {
      intro ; apply isapropunit.
    }
    use subtypePath.
    {
      intro ; apply setoid_cat.
    }
    use setoid_morphism_eq.
    intro x.
    induction x as [ x | s p IHp ].
    - exact (fromempty x).
    - pose (alg_map_commute_setoid
              (pr1 φ₁)
              (@container_to_setoid _ initial_setoid_carrier (s ,, p)))
        as q₁.
      pose (alg_map_commute_setoid
              (pr1 φ₂)
              (@container_to_setoid _ initial_setoid_carrier (s ,, p)))
        as q₂.
      cbn in q₁, q₂.
      refine (q₁ @ _ @ !q₂) ; clear q₁ q₂.
      do 2 apply maponpaths.
      use setoid_morphism_eq ; cbn.
      intro.
      exact (IHp x).
  Qed.

  Definition initial_setoid_algebra_existence_carrier
             (Y : hit_setoid_algebra Σ)
    : initial_setoid_carrier → alg_carrier_setoid (pr1 Y).
  Proof.
    cbn ; intro x.
    induction x as [ x | s x IHx ].
    - exact (fromempty x).
    - apply (algebra_map_setoid (pr1 Y)).
      simple refine (s ,, _) ; simpl.
      use make_setoid_morphism.
      + exact IHx.
      + abstract
          (simpl ;
           intros ? ? p ;
           induction p ;
           apply (id _)%setoid).
  Defined.

  Definition initial_setoid_algebra_existence_carrier_endpoint
             (Y : hit_setoid_algebra Σ)
             {i : path_index Σ}
             (p : path_arg Σ i → initial_setoid_carrier_set)
             (x : W (point_constr Σ) (path_arg Σ i))
    : initial_setoid_algebra_existence_carrier
        Y
        (sem_endpoint initial_setoid_carrier_set_sup i p x)
      ≡
      sem_endpoint_setoid
        (algebra_map_setoid (pr1 Y))
        i
        (λ z, initial_setoid_algebra_existence_carrier Y (p z))
        x.
  Proof.
    induction x as [ x | s q IHq ].
    - apply (id _)%setoid.
    - cbn.
      use (map_eq (algebra_map_setoid (pr1 Y))).
      simple refine (idpath _ ,, _) ; cbn.
      intro x.
      apply IHq.
  Qed.
    
  Definition initial_setoid_algebra_existence_alg_on_eq
             (Y : hit_setoid_algebra Σ)
             {x y : alg_carrier_setoid (pr1 initial_setoid_algebra)}
             (p : x ≡ y)
    : initial_setoid_algebra_existence_carrier Y x
      ≡
      initial_setoid_algebra_existence_carrier Y y.
  Proof.
    simpl in p.
    use (hinhuniv _ p).
    clear p ; intro p.
    induction p.
    - exact (id _)%setoid.
    - exact (!IHp)%setoid.
    - exact (IHp1 @ IHp2)%setoid.
    - cbn.
      refine (map_eq (algebra_map_setoid (pr1 Y)) _) ; cbn.
      exact (idpath _ ,, X).
    - pose (h := pr2 Y i (λ z, initial_setoid_algebra_existence_carrier _ (p z))).
      refine (_ @ h @ !_)%setoid ; clear h.
      + apply initial_setoid_algebra_existence_carrier_endpoint.
      + apply initial_setoid_algebra_existence_carrier_endpoint.
  Qed.

  Definition initial_setoid_algebra_existence_setoid_morphism
             (Y : hit_setoid_algebra Σ)
    : setoid_morphism
        (alg_carrier_setoid (pr1 initial_setoid_algebra))
        (alg_carrier_setoid (pr1 Y)).
  Proof.
    use make_setoid_morphism.
    - exact (initial_setoid_algebra_existence_carrier Y).
    - exact (@initial_setoid_algebra_existence_alg_on_eq Y).
  Defined.

  Definition initial_setoid_algebra_existence_commute
             (Y : hit_setoid_algebra Σ)
             (x : ⦃ point_constr Σ ⦄
                    (alg_carrier_setoid (pr1 initial_setoid_algebra)))
    : initial_setoid_algebra_existence_carrier
        Y
        (initial_setoid_constructor_carrier x)
      =
      algebra_map_setoid
        (pr1 Y)
        (interpret_container_setoid_morphism
           (point_constr Σ)
           (initial_setoid_algebra_existence_setoid_morphism Y) x).
  Proof.
    cbn.
    do 2 apply maponpaths ; use setoid_morphism_eq ; cbn.
    intro p.
    apply idpath.
  Qed.

  Definition initial_setoid_algebra_existence
             (Y : hit_setoid_algebra Σ)
    : hit_setoid_algebra Σ ⟦ initial_setoid_algebra, Y ⟧.
  Proof.
    simple refine (_ ,, tt).
    use make_hit_setoid_prealgebra_mor.
    - exact (initial_setoid_algebra_existence_setoid_morphism Y).
    - exact (initial_setoid_algebra_existence_commute Y).
  Defined.

  Definition initial_setoid_algebra_isInitial
    : isInitial _ initial_setoid_algebra.
  Proof.
    use make_isInitial.
    intro Y.
    use iscontraprop1.
    - exact (initial_setoid_algebra_uniqueness Y).
    - exact (initial_setoid_algebra_existence Y).
  Defined.

  Definition intial_ob_hit_setoid_algebra
    : Initial (hit_setoid_algebra Σ).
  Proof.
    use make_Initial.
    - exact initial_setoid_algebra.
    - exact initial_setoid_algebra_isInitial.
  Defined.
End InitialSetoidAlgebra.

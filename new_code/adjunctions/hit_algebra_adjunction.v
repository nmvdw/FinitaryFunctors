(**
Here we define two constructions for adjunctions.
The first construction says how to get an adjunction between the category of algebras.
The second construction factors an adjunction through the full subcategory.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Univalence.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import prelude.
Require Import setoids.base.
Require Import setoids.setoid_category.
Require Import syntax.containers.
Require Import syntax.hit_signature.
Require Import syntax.W_types.
Require Import algebra.setoid_algebra.
Require Import algebra.set_algebra.
Require Import adjunctions.adjunction_constructions.

Open Scope cat.

Section HITAdjunction.
  Variable (Σ : hit_signature)
           (Σ_finite : is_finitary_hit Σ).

  Definition quotient_container_commute_data
    : nat_trans_data
        (quotient ∙ container_to_functor (point_constr Σ))
        (container_to_setoid_functor (point_constr Σ) ∙ quotient).
  Proof.
    intros X.
    cbn.
    intro x.
  Admitted.

  Definition quotient_container_commute_is_nat_trans
    : is_nat_trans _ _ quotient_container_commute_data.
  Proof.
    intros X Y f.
  Admitted.

  Definition quotient_container_commute
    : quotient ∙ container_to_functor (point_constr Σ)
      ⟹
      container_to_setoid_functor (point_constr Σ) ∙ quotient.
  Proof.
    use make_nat_trans.
    - exact quotient_container_commute_data.
    - exact quotient_container_commute_is_nat_trans.
  Defined.

  Definition path_setoid_container_commute_data
    : nat_trans_data
        (path_setoid ∙ container_to_setoid_functor (point_constr Σ))
        (container_to_functor (point_constr Σ) ∙ path_setoid).
  Proof.
    intros X.
    use make_setoid_morphism.
    - cbn ; intro x.
      refine (pr1 x ,, λ p, _).
      exact (pr2 x p).
    - abstract
        (cbn ; intros x₁ x₂ p ;
         induction x₁ as [x₁ y₁] ;
         induction x₂ as [x₂ y₂] ;
         induction p as [p₁ p₂] ;
         cbn in * ;
         induction p₁ ;
         cbn in * ;
         apply maponpaths ;
         use funextsec ;
         exact p₂).
  Defined.

  Definition path_setoid_container_commute_is_nat_trans
    : is_nat_trans _ _ path_setoid_container_commute_data.
  Proof.
    intros X Y f.
    use setoid_morphism_eq.
    intro x ; cbn.
    apply idpath.
  Qed.

  Definition path_setoid_container_commute
    : path_setoid ∙ container_to_setoid_functor (point_constr Σ)
      ⟹
      container_to_functor (point_constr Σ) ∙ path_setoid.
  Proof.
    use make_nat_trans.
    - exact path_setoid_container_commute_data.
    - exact path_setoid_container_commute_is_nat_trans.
  Defined.

  Definition hit_prealg_coherency_counit
             (X : hSet)
    : quotient_container_commute (path_setoid X)
      · # quotient (path_setoid_container_commute X)
      · quotient_counit (container_to_functor (point_constr Σ) X)
      =
      # (container_to_functor (point_constr Σ)) (quotient_counit X).
  Proof.
    use funextsec.
  Admitted.

  Definition hit_prealg_coherency_unit
             (X : setoid)
    : quotient_unit (container_to_setoid_functor (point_constr Σ) X)
      =
      # (container_to_setoid_functor (point_constr Σ)) (quotient_unit X)
      · path_setoid_container_commute (quotient X)
      · # path_setoid (quotient_container_commute X).
  Proof.
    use setoid_morphism_eq.
    intro x ; cbn.
  Admitted.
    
  Definition hit_prealg_disp_adjunction
    : disp_adjunction
        quotient_adjunction
        (fun_algebra_disp_cat (container_to_setoid_functor (point_constr Σ)))
        (fun_algebra_disp_cat (container_to_functor (point_constr Σ))).
  Proof.
    use fun_algebra_disp_adjunction.
    - exact quotient_container_commute.
    - exact path_setoid_container_commute.
    - exact hit_prealg_coherency_counit.
    - exact hit_prealg_coherency_unit.
  Defined.

  Definition hit_prealg_adjunction
    : adjunction
        (hit_setoid_prealgebra Σ)
        (hit_prealgebra Σ)
    := total_adjunction hit_prealg_disp_adjunction.

  Definition setoid_algebra_is_algebra
             (X : hit_setoid_prealgebra Σ)
             (HX : is_hit_setoid_algebra X)
    : is_hit_algebra (left_functor hit_prealg_adjunction X).
  Proof.
    intros i p.
  Admitted.

  Definition algebra_is_setoid_algebra
             (X : hit_prealgebra Σ)
             (HX : is_hit_algebra X)
    : is_hit_setoid_algebra (right_functor hit_prealg_adjunction X).
  Proof.
    intros i p.
    exact (HX i p).
  Qed.

  Definition hit_algebra_disp_adjunction
    : disp_adjunction
        hit_prealg_adjunction
        (hit_setoid_algebra_disp_cat Σ)
        (hit_algebra_disp_cat Σ).
  Proof.
    use disp_full_sub_adjunction.
    - exact setoid_algebra_is_algebra.
    - exact algebra_is_setoid_algebra.
  Defined.
End HITAdjunction.

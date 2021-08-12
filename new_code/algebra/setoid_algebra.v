Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Isos.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.limits.binproducts.
Require Import UniMath.CategoryTheory.limits.bincoproducts.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

Require Import prelude.
Require Import syntax.containers.
Require Import syntax.hit_signature.
Require Import syntax.W_types.
Require Import setoids.base.
Require Import setoids.setoid_category.

Local Open Scope container_scope.
Local Open Scope cat.

Definition dependent_sum_hrel
           (X : hSet)
           (Y : X → setoid)
  : hrel (∑ x : X, Y x).
Proof.
  intros x y.
  use make_hProp.
  - exact (∑ (p : pr1 x = pr1 y), transportf Y p (pr2 x) ≡ pr2 y).
  - abstract
      (use isaproptotal2 ;
       [ intro ; apply isaprop_setoid_eq
       | intros ; apply X ]).
Defined.

Definition dependent_sum_iseqrel
           (X : hSet)
           (Y : X → setoid)
  : iseqrel (dependent_sum_hrel X Y).
Proof.
  repeat split.
  - intros x₁ x₂ x₃ p q.
    induction x₁ as [x₁ y₁].
    induction x₂ as [x₂ y₂].
    induction x₃ as [x₃ y₃].
    induction p as [p₁ p₂].
    induction q as [q₁ q₂].
    simpl in *.
    induction p₁ ; induction q₁.
    cbn in *.
    exact (idpath _ ,, p₂ @ q₂)%setoid.
  - intro x.
    exact (idpath _ ,, id _)%setoid.
  - intros x₁ x₂ p.
    induction x₁ as [x₁ y₁].
    induction x₂ as [x₂ y₂].
    induction p as [p₁ p₂].
    simpl in *.
    induction p₁.
    exact (idpath _ ,, !p₂)%setoid.
Qed.

Definition dependent_sum_eq_rel
           (X : hSet)
           (Y : X → setoid)
  : eqrel (∑ x : X, Y x).
Proof.
  use make_eqrel.
  - exact (dependent_sum_hrel X Y).
  - exact (dependent_sum_iseqrel X Y).
Defined.

Definition dependent_sum_setoid
           (X : hSet)
           (Y : X → setoid)
  : setoid.
Proof.
  use make_setoid.
  - exact (∑ (x : X), Y x)%set.
  - exact (dependent_sum_eq_rel X Y).
Defined.

Definition interpret_container_setoid
           (C : container)
           (X : setoid)
  : setoid
  := dependent_sum_setoid
       (shapes C)
       (λ s, setoid_exp (path_setoid (positions C s)) X).

Notation "⦃ C ⦄ X" := (interpret_container_setoid C X) (at level 70) : container_scope.
(** \{{ and \}} *)

Definition interpret_container_setoid_morphism
           (C : container)
           {X Y : setoid}
           (f : setoid_morphism X Y)
  : setoid_morphism (⦃ C ⦄ X) (⦃ C ⦄ Y).
Proof.
  use make_setoid_morphism.
  - simpl.
    intro x.
    simple refine (pr1 x ,, _).
    use make_setoid_morphism.
    + intro s ; cbn in *.
      exact (f (pr2 x s)).
    + intros y₁ y₂ p ; cbn in *.
      exact (map_eq f (map_eq (pr2 x) p)).
  - simpl.
    intros x₁ x₂ p.
    induction x₁ as [x₁ y₁].
    induction x₂ as [x₂ y₂].
    induction p as [p₁ p₂].
    simpl in *.
    induction p₁.
    cbn in *.
    simple refine (idpath _ ,, _).
    intro x ; cbn.
    exact (map_eq f (p₂ x)).
Defined.

Definition container_to_setoid_functor_data
           (C : container)
  : functor_data setoid_cat setoid_cat.
Proof.
  use make_functor_data.
  - exact (λ X, ⦃ C ⦄ X).
  - exact (λ _ _ f, interpret_container_setoid_morphism C f).
Defined.

Definition container_to_setoid_is_functor
           (C : container)
  : is_functor (container_to_setoid_functor_data C).
Proof.
  split.
  - intro X.
    use setoid_morphism_eq ; cbn.
    intro x ; cbn.
    refine (maponpaths (λ z, pr1 x ,, z) _).
    unfold make_setoid_morphism.
    use subtypePath.
    {
      intro.
      do 3 (use impred ; intro).
      apply isaprop_setoid_eq.
    }
    apply idpath.
  - intros X Y Z f g.
    use setoid_morphism_eq ; cbn.
    intro x ; cbn.
    refine (maponpaths (λ z, pr1 x ,, z) _).
    unfold make_setoid_morphism.
    use subtypePath.
    {
      intro.
      do 3 (use impred ; intro).
      apply isaprop_setoid_eq.
    }
    apply idpath.
Qed.

Definition container_to_setoid_functor
           (C : container)
  : setoid_cat ⟶ setoid_cat.
Proof.
  use make_functor.
  - exact (container_to_setoid_functor_data C).
  - exact (container_to_setoid_is_functor C).
Defined.

(** Relevant builders *)
Definition shape_of_setoid
           {C : container}
           {X : setoid}
           (x : ⦃ C ⦄ X)
  : shapes C
  := pr1 x.

Definition position_of_setoid
           {C : container}
           {X : setoid}
           (x : ⦃ C ⦄ X)
  : positions C (shape_of_setoid x) → X
  := pr12 x.

Definition cpair_setoid
           {C : container}
           {X : setoid}
           (s : shapes C)
           (f : setoid_morphism
                  (path_setoid (positions C s))
                  X)
  : ⦃ C ⦄ X
  := s ,, f.

Definition sem_endpoint_setoid
           {Σ : hit_signature}
           {X : setoid}
           (c : setoid_morphism (⦃ point_constr Σ ⦄ X) X)
           (i : path_index Σ)
           (var : path_arg Σ i → X)
           (x : W (point_constr Σ) (path_arg Σ i))
  : X.
Proof.
  induction x as [ v | s p IHp ].
  - exact (var v).
  - simple refine (c (s ,, _)).
    use make_setoid_morphism ; cbn.
    + exact IHp.
    + intros x y q.
      induction q.
      exact (id _)%setoid.
Defined.

Definition hit_algebra_setoid_disp_cat
           (Σ : hit_signature)
  : disp_cat
      (total_category
         (fun_algebra_disp_cat
            (container_to_setoid_functor (point_constr Σ)))).
Proof.
  use disp_full_sub.
  intros X.
  induction X as [X c] ; simpl in *.
  exact (∏ (i : path_index Σ)
           (p : path_arg Σ i → X),
         sem_endpoint_setoid c i p (path_lhs Σ i)
         ≡
         sem_endpoint_setoid c i p (path_rhs Σ i))%type.
Defined.

Definition hit_algebra_setoid
           (Σ : hit_signature)
  : category
  := total_category (hit_algebra_setoid_disp_cat Σ).

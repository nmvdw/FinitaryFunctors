(**
Here we define two constructions for adjunctions.
The first construction says how to get an adjunction between the category of algebras.
The second construction factors an adjunction through the full subcategory.
 *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.FiniteSets.

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

Local Open Scope cat.
Local Open Scope stn.

Definition TODO {A : UU} : A.
Admitted.

Definition setquot_of_fun_space
           {X Y : UU}
           {eqY : eqrel Y}
           (f : setquot (eqrel_fun_space X eqY))
  : X → setquot eqY.
Proof.
  intro x.
  simple refine (setquotfun _ _ _ _ f).
  - exact (λ g, g x).
  - exact (λ _ _ p, p x).
Defined.

Definition setquot_of_fun_space_inv
           {X Y : UU}
           {eqY : eqrel Y}
           (n : nat)
           (e : X ≃ stn n)
           (f : X → setquot eqY)
  : setquot (eqrel_fun_space X eqY).
Proof.
  revert X Y eqY e f.
  induction n as [ | n IHn ] ; intros X Y eqY e f.
  - apply setquotpr.
    exact (λ x, fromempty (weqstn0toempty (e x))).
  - pose (z := f (invmap e (weqfromcoprodofstn_map 1 n (inl (invmap weqstn1tounit tt))))).
    specialize (IHn
                  (stn n) Y
                  eqY (idweq _)
                  (λ z, f (invmap e (weqfromcoprodofstn_map 1 n (inr z))))).
    simple refine (setquotuniv
                     _
                     (make_hSet
                        (setquot (eqrel_fun_space X eqY))
                        (isasetsetquot _))
                     _ _
                     z)
    ; clear z.
    + intros z.
      simple refine (setquotuniv
                       _
                       (make_hSet
                          (setquot (eqrel_fun_space X eqY))
                          (isasetsetquot _))
                       _ _
                       IHn)
      ; clear IHn.
      * intros IHn.
        apply setquotpr.
        refine (λ x, _).
        destruct (invmap (weqfromcoprodofstn 1 n) (e x)) as [ s | s ].
        ** exact z.
        ** exact (IHn s).
      * abstract
          (intros g₁ g₂ r ;
           apply iscompsetquotpr ;
           intro x ;
           cbn ;
           induction (weqfromcoprodofstn_invmap 1 n (e x)) as [ s | s ] ;
           [ apply eqY
           | exact (r s) ]).
    + abstract
        (intros g₁ g₂ r ;
         use (setquotunivprop' (λ z, _ = _) _ _ IHn) ;
         [ intro ;
           apply isasetsetquot
         | intros h ;
           apply iscompsetquotpr ;
           intros x ;
           induction (invmap (weqfromcoprodofstn 1 n) (e x)) as [ s | s ] ;
           [ exact r
           | cbn ;
             apply eqY ]]).
Defined.


Section QuotientCommutation.
  Variable (C : container).
  
  Definition container_quotient_map
    : nat_trans_data
        (container_to_setoid_functor C ∙ quotient)
        (quotient ∙ container_to_functor C).
  Proof.
    intros X.
    use setquotuniv ; cbn.
    - intros x.
      simple refine (pr1 x ,, (λ p, setquotpr (carrier_eq X) _)) ; cbn.
      exact (pr2 x p).
    - abstract
        (intros x₁ x₂ p ; cbn ; cbn in p ;
         induction x₁ as [ x₁ y₁ ] ; induction x₂ as [ x₂ y₂ ] ;
         cbn in p ;
         induction p as [ p q ] ;
         induction p ; cbn in q ;
         apply maponpaths ;
         use funextsec ;
         intro z ;
         use iscompsetquotpr ; cbn ;
         exact (q z)).
  Defined.

  Definition container_quotient_is_nat_trans
    : is_nat_trans _ _ container_quotient_map.
  Proof.
    intros X Y f.
    use funextsec.
    use setquotunivprop'.
    - intro.
      apply (interpret_container C (quotient_setoid_ob Y)).
    - intros x ; cbn.
      unfold interpret_container_map, cpair ; cbn.
      apply idpath.
  Qed.

  Definition container_quotient
    : container_to_setoid_functor C ∙ quotient
      ⟹
      quotient ∙ container_to_functor C.
  Proof.
    use make_nat_trans.
    - exact container_quotient_map.
    - exact container_quotient_is_nat_trans.
  Defined.

  Definition container_quotient_weq
             (HC : is_finitary C)
             (X : setoid)
    : ((container_to_setoid_functor C ∙ quotient) X : hSet)
      ≃
      ((quotient ∙ container_to_functor C) X : hSet).
  Proof.
    use make_weq.
    - exact (container_quotient_map X).
    - unfold is_finitary in HC.
      use gradth.
      + intros x.
        induction x as [ x y ].
        pose (setquot_of_fun_space_inv TODO TODO y) as s.
        simple refine (setquotuniv _ _ _ _ s) ; clear s.
        ** intros f.
           apply setquotpr.
           refine (x ,, _).
           use make_setoid_morphism.
           *** exact f.
           *** abstract
                 (cbn ; intros ? ? p ;
                  induction p ;
                  apply (id _)%setoid).
        ** abstract
             (intros g₁ g₂ p ;
              use iscompsetquotpr ;
              simple refine (idpath _ ,, _) ; cbn ;
              intro z ;
              exact (p z)).
      + use setquotunivprop'.
        * intros x.
          apply isasetsetquot.
        * intros x.
          cbn.
          induction x as [ x y ].
          simpl.
          apply TODO.
      + apply TODO.
  Defined.
  
  Definition container_quotient_is_nat_iso
             (HC : is_finitary C)
    : is_nat_iso container_quotient
    := λ X, hset_equiv_is_iso
              _ _
              (container_quotient_weq HC X).
    
  Definition container_quotient_iso
             (HC : is_finitary C)
    : nat_iso
        (container_to_setoid_functor C ∙ quotient)
        (quotient ∙ container_to_functor C).
  Proof.
    use make_nat_iso.
    - exact container_quotient.
    - exact (container_quotient_is_nat_iso HC).
  Defined.
End QuotientCommutation.

Section HITAdjunction.
  Variable (Σ : hit_signature)
           (Σ_finite : is_finitary_hit Σ).

  (*
  Definition quotient_container_commute_data
    : nat_trans_data
        (quotient ∙ container_to_functor (point_constr Σ))
        (container_to_setoid_functor (point_constr Σ) ∙ quotient).
  Proof.
    intros X.
    intros x.
    (*
    induction x as [ x f ].
    simpl in X.
    assert (positions (point_constr Σ) x → X) as g.
    {
      admit.
    }
    apply setquotpr.
    simpl.
    simple refine (x ,, _) ; simpl.
    use make_setoid_morphism.
    - exact g.
    - simpl.
      intros ? ? p.
      induction p.
      apply (id _)%setoid.
     *)
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
   *)

  Definition quotient_container_commute
    : quotient ∙ container_to_functor (point_constr Σ)
      ⟹
      container_to_setoid_functor (point_constr Σ) ∙ quotient
    := nat_iso_inv
         (container_quotient_iso
            (point_constr Σ)
            (pr1 Σ_finite)).

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

  Definition hit_prealg_coherency_counit_help
             (X : hSet)
             (z : quotient
                    ((path_setoid ∙ container_to_setoid_functor (point_constr Σ)) X) : hSet)
    : quotient_counit
        (interpret_container (point_constr Σ) X)
        (#quotient
          (path_setoid_container_commute X)
          z)
      =
      # (container_to_functor (point_constr Σ)) (quotient_counit X)
        (container_quotient_weq
           (point_constr Σ)
           (pr1 Σ_finite)
           (make_setoid (path_rel X))
           z).
  Proof.
    revert z.
    use setquotunivprop'.
    - intro x.
      apply (container_to_functor (point_constr Σ) X).
    - intro z.
      apply idpath.
  Qed.

  Definition hit_prealg_coherency_counit
             (X : hSet)
    : quotient_container_commute (path_setoid X)
      · # quotient (path_setoid_container_commute X)
      · quotient_counit (container_to_functor (point_constr Σ) X)
      =
      # (container_to_functor (point_constr Σ)) (quotient_counit X).
  Proof.
    use funextsec.
    intros z.
    refine (!_).
    etrans.
    {
      apply maponpaths.
      exact (!(homotweqinvweq
                 (container_quotient_weq
                    (point_constr Σ)
                    (pr1 Σ_finite)
                    (make_setoid (path_rel X)))
                 z)).
    }
    refine (!_).
    exact (hit_prealg_coherency_counit_help
             X
             (invmap
                (container_quotient_weq
                   (point_constr Σ)
                   (pr1 Σ_finite)
                   (make_setoid (path_rel X))) z)).
  Time Qed.

  Definition hit_prealg_coherency_unit
             (X : setoid)
    : quotient_unit (container_to_setoid_functor (point_constr Σ) X)
      =
      # (container_to_setoid_functor (point_constr Σ)) (quotient_unit X)
      · path_setoid_container_commute (quotient X)
      · # path_setoid (quotient_container_commute X).
  Proof.
    use setoid_morphism_eq.
    intro x.
    use pathsweq1.
    apply idpath.
  Qed.
    
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
    cbn in p.
    pose (HX i).
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

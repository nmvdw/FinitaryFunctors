Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.limits.initial.
Require Import UniMath.CategoryTheory.Monads.Monads.

Require Import prelude.
Require Import syntax.containers.
Require Import syntax.hit_signature.
Require Import syntax.W_types.
Require Import algebra.set_algebra.

Local Open Scope container_scope.
Local Open Scope cat.

Section FreeAlgebra.
  Variable (Σ : hit_signature)
           (A : hSet).

  Definition free_point_constr
    : container
    := point_constr Σ ⊕ A.

  Definition free_path_arg
    : container
    := pr12 Σ.

  Definition to_free_point_constr
             {X : hSet}
             (x : W (point_constr Σ) X)
    : W free_point_constr X.
  Proof.
    induction x as [ x | s p IHp ].
    - exact (var x).
    - use sup.
      + exact (inl s).
      + exact IHp.
  Defined.
  
  Definition free_sig
    : hit_signature.
  Proof.
    use make_hit_signature.
    - exact free_point_constr.
    - exact free_path_arg.
    - exact (λ s, to_free_point_constr (path_lhs Σ s)).
    - exact (λ s, to_free_point_constr (path_rhs Σ s)).
  Defined.

  Definition is_finitary_free_sig
             (HΣ : is_finitary_hit Σ)
    : is_finitary_hit free_sig.
  Proof.
    split.
    - use is_finitary_sum_container.
      + apply HΣ.
      + exact (is_finitary_constant_container A).
    - apply HΣ.
  Qed.

  Section FreeAlgebra.
    Variable (X : hit_algebra free_sig).

    Definition free_carrier
      : hSet
      := pr11 X.

    Definition free_inclusion
               (a : A)
      : free_carrier
      := pr21 X (inr a ,, fromempty).

    Definition free_constr
               (x : ⟦ point_constr Σ ⟧ free_carrier)
      : free_carrier
      := pr21 X (inl (pr1 x) ,, pr2 x).

    Definition free_to_sig_prealgebra
      : hit_prealgebra Σ
      := free_carrier ,, free_constr.

    Definition free_is_hit_algebra_help
               {i : path_index Σ}
               (p : path_arg Σ i → alg_carrier free_to_sig_prealgebra)
               (w : W (point_constr Σ) (path_arg Σ i))
      : sem_endpoint (algebra_map free_to_sig_prealgebra) i p w
        =
        sem_endpoint (algebra_map (pr1 X)) i p (to_free_point_constr w).
    Proof.
      induction w as [ x | s q IHq ].
      - apply idpath.
      - cbn.
        unfold free_constr.
        do 2 apply maponpaths.
        use funextsec.
        intro z ; cbn.
        apply IHq.
    Qed.
    
    Definition free_is_hit_algebra
      : is_hit_algebra free_to_sig_prealgebra.
    Proof.
      intros i p.
      exact (free_is_hit_algebra_help _ _
             @ pr2 X i p
             @ !(free_is_hit_algebra_help _ _)).
    Qed.

    Definition free_to_sig_algebra
      : hit_algebra Σ.
    Proof.
      simple refine (free_to_sig_prealgebra ,, _).
      exact free_is_hit_algebra.
    Defined.
  End FreeAlgebra.

  Section MakeFreeAlgebra.
    Context (X : hit_algebra Σ)
            (inc : A → alg_carrier (pr1 X)).

    Definition make_free_prealgebra
      : hit_prealgebra free_sig.
    Proof.
      simple refine (_ ,, _) ; simpl.
      - exact (alg_carrier (pr1 X)).
      - intro x.
        induction x as [ s p ].
        induction s as [ s | a ].
        + exact (pr21 X (s ,, p)).
        + exact (inc a).
    Defined.

    Definition make_free_is_hit_algebra_help
               {i : path_index free_sig}
               (p : path_arg free_sig i → alg_carrier make_free_prealgebra)
               (w : W (point_constr Σ) (path_arg Σ i))
      : sem_endpoint
          (algebra_map make_free_prealgebra)
          i p
          (to_free_point_constr w)
        =
        sem_endpoint (algebra_map (pr1 X)) i p w.
    Proof.
      induction w as [ x | s q IHq ].
      - apply idpath.
      - cbn.
        do 2 apply maponpaths.
        use funextsec.
        intro z.
        apply IHq.
    Qed.
    
    Definition make_free_is_hit_algebra
      : is_hit_algebra make_free_prealgebra.
    Proof.
      intros i p.
      refine (_ @ pr2 X i p @ !_).
      - apply make_free_is_hit_algebra_help.
      - apply make_free_is_hit_algebra_help.
    Qed.
    
    Definition make_free_algebra
      : hit_algebra free_sig
      := make_free_prealgebra ,, make_free_is_hit_algebra.
  End MakeFreeAlgebra.

  Section FreeMor.
    Context {X Y : hit_algebra free_sig}
            (f : X --> Y).

    Definition free_mor_carrier
      : free_to_sig_algebra X --> free_to_sig_algebra Y.
    Proof.
      simple refine ((pr11 f ,, _) ,, tt) ; simpl.
      abstract
        (use funextsec ;
         intro x;  
         induction x as [x y] ;
         exact (eqtohomot (pr21 f) (inl x ,, y))).
    Defined.

    Definition free_mor_inclusion
               (a : A)
      : pr11 free_mor_carrier (free_inclusion X a)
        =
        free_inclusion Y a.
    Proof.
      pose (p := eqtohomot (pr21 f) (inr a ,, fromempty)).
      refine (p @ _) ; cbn ; unfold interpret_container_map ; cbn.
      unfold free_inclusion.
      do 2 apply maponpaths.
      use funextsec.
      intro z.
      induction z.
    Qed.    
  End FreeMor.

  Definition make_free_mor
             {X Y : hit_algebra free_sig}
             (f : free_to_sig_algebra X --> free_to_sig_algebra Y)
             (p : ∏ (a : A),
                  pr11 f (free_inclusion X a)
                  =
                  free_inclusion Y a)
    : X --> Y.
  Proof.
    simple refine ((pr11 f ,, _) ,, tt) ; cbn.
    abstract
      (use funextsec ;
       intro x ;
       induction x as [ x y ] ;
       induction x as [ x | a ] ;
       [ exact (eqtohomot (pr21 f) (x ,, y))
       |  refine (_ @ p a @ _) ;
          [ unfold free_inclusion ; cbn ;
            do 3 apply maponpaths ;
            use funextsec ;
            intro z ;
            induction z
        | unfold free_inclusion, interpret_container_map ; cbn ;
          do 2 apply maponpaths ;
          use funextsec ;
          intro z ;
          induction z ]]).
  Defined.
End FreeAlgebra.

(** Free algebra adjunction assuming that initial algebras exist *)
Section FreeAlgebraAdj.
  Context (Σ : hit_signature)
          (free_alg : ∏ (A : hSet),
                      Initial (hit_algebra (free_sig Σ A))).

  Definition free_algebra_functor_obj
             (A : hSet)
    : hit_algebra Σ
    := free_to_sig_algebra _ _ (InitialObject (free_alg A)).

  Definition free_algebra_ump
             {A : hSet}
             (X : hit_algebra Σ)
             (i : A → alg_carrier (pr1 X))
    : free_to_sig_algebra Σ A (free_alg A)
      -->
      free_to_sig_algebra Σ A (make_free_algebra Σ A X i)
    := free_mor_carrier
            _ _
            (InitialArrow (free_alg A) (make_free_algebra _ _ X i)).

  Definition free_algebra_ump_commute
             {A : hSet}
             (X : hit_algebra Σ)
             (i : A → alg_carrier (pr1 X))
             (a : A)
    : pr11 (free_algebra_ump X i) (free_inclusion _ _ _ a) = i a.
  Proof.
    apply free_mor_inclusion.    
  Qed.

  Definition free_algebra_ump_eq
             {A : hSet}
             (X : hit_algebra Σ)
             (i : A → alg_carrier (pr1 X))
             (f : free_to_sig_algebra Σ A (free_alg A)
                  -->
                  free_to_sig_algebra Σ A (make_free_algebra Σ A X i))
             (p : ∏ (a : A), pr11 f (free_inclusion _ _ _ a) = i a)
    : free_algebra_ump X i = f.
  Proof.
    pose (InitialArrowUnique
            (free_alg A)
            (make_free_algebra _ _ X i)
            (make_free_mor _ _ f p))
      as q.
    use hit_algebra_map_eq.
    intro x.
    exact (!(maponpaths (λ g, pr11 g x) q)).
  Qed.

  Definition free_algebra_maps_eq
             {A : hSet}
             (X : hit_algebra Σ)
             (i : A → alg_carrier (pr1 X))
             {f g : free_to_sig_algebra Σ A (free_alg A)
                    -->
                    free_to_sig_algebra Σ A (make_free_algebra Σ A X i)}
             (p : ∏ (a : A), pr11 f (free_inclusion _ _ _ a) = i a)
             (q : ∏ (a : A), pr11 g (free_inclusion _ _ _ a) = i a)
    : f = g.
  Proof.
    etrans.
    {
      refine (!_).
      exact (free_algebra_ump_eq X i f p).
    }
    apply free_algebra_ump_eq.
    exact q.
  Qed.
  
  Definition free_algebra_functor_mor
             {A B : hSet}
             (f : A → B)
    : free_algebra_functor_obj A --> free_algebra_functor_obj B
    := free_algebra_ump
         (free_to_sig_algebra _ _ (free_alg B))
         (λ a, free_inclusion _ _ _ (f a)).

  Definition free_algebra_functor_data
    : functor_data HSET (hit_algebra Σ).
  Proof.
    use make_functor_data.
    - exact free_algebra_functor_obj.
    - exact @free_algebra_functor_mor.
  Defined.

  Definition free_algebra_is_functor
    : is_functor free_algebra_functor_data.
  Proof.
    split.
    - intro X.
      use (free_algebra_ump_eq (free_to_sig_algebra Σ X (free_alg X))).
      intros a ; cbn.
      apply idpath.
    - intros X Y Z f g.
      use (free_algebra_ump_eq (free_to_sig_algebra Σ Z (free_alg Z))).
      intros a ; cbn -[free_algebra_ump] ; unfold free_algebra_functor_mor.
      etrans.
      {
        apply maponpaths.
        apply (free_algebra_ump_commute
                 (free_to_sig_algebra Σ Y (free_alg Y))).
      }
      etrans.
      {
        apply (free_algebra_ump_commute
                 (free_to_sig_algebra Σ Z (free_alg Z))).
      }
      apply idpath.
  Qed.
  
  Definition free_algebra_functor
    : HSET ⟶ hit_algebra Σ.
  Proof.
    use make_functor.
    - exact free_algebra_functor_data.
    - exact free_algebra_is_functor.
  Defined.

  Definition forgetful_data
    : functor_data (hit_algebra Σ) HSET.
  Proof.
    use make_functor_data.
    - exact (λ X, pr11 X).
    - exact (λ _ _ f, pr11 f).
  Defined.

  Definition forgetful_is_functor
    : is_functor forgetful_data.
  Proof.
    split ; intro ; intros ; apply idpath.
  Qed.
      
  Definition forgetful
    : hit_algebra Σ ⟶ HSET.
  Proof.
    use make_functor.
    - exact forgetful_data.
    - exact forgetful_is_functor.
  Defined.

  Definition free_algebra_unit_data
    : nat_trans_data
        (functor_identity _)
        (free_algebra_functor ∙ forgetful).
  Proof.
    intros A ; cbn.
    exact (free_inclusion _ _ (free_alg A)).
  Defined.

  Definition free_algebra_unit_is_nat_trans
    : is_nat_trans _ _ free_algebra_unit_data.
  Proof.
    intros A B f.
    use funextsec ; intro a.
    pose (Balg := make_free_algebra
                    _ _
                    (free_to_sig_algebra _ _ (free_alg B))
                    (λ a, free_inclusion _ _ _ (f a))).
    pose (p := free_mor_inclusion _ _ (InitialArrow (free_alg A) Balg) a).
    exact (!p).
  Qed.

  Definition free_algebra_unit
    : functor_identity _ ⟹ free_algebra_functor ∙ forgetful.
  Proof.
    use make_nat_trans.
    - exact free_algebra_unit_data.
    - exact free_algebra_unit_is_nat_trans.
  Defined.

  Definition free_algebra_counit_data
    : nat_trans_data (forgetful ∙ free_algebra_functor) (functor_identity _).
  Proof.
    intros X.
    exact (free_algebra_ump X (λ x, x)).
  Defined.

  Definition free_algebra_counit_is_nat_trans
    : is_nat_trans _ _ free_algebra_counit_data.
  Proof.
    intros X Y f.
    use free_algebra_maps_eq.
    - exact (pr11 f).
    - cbn -[free_algebra_ump].
      intro a.
      unfold free_algebra_functor_mor.
      etrans.
      {
        apply maponpaths.
        apply (free_algebra_ump_commute
                 (free_to_sig_algebra Σ (pr11 Y) (free_alg (pr11 Y)))).
      }
      unfold free_algebra_counit_data.
      etrans.
      {
        apply (free_algebra_ump_commute Y).
      }
      apply idpath.
    - cbn -[free_algebra_ump].
      intros a.
      unfold free_algebra_counit_data.
      etrans.
      {
        apply maponpaths.
        apply (free_algebra_ump_commute X).
      }
      apply idpath.
  Qed.

  Definition free_algebra_counit
    : forgetful ∙ free_algebra_functor ⟹ functor_identity _.
  Proof.
    use make_nat_trans.
    - exact free_algebra_counit_data.
    - exact free_algebra_counit_is_nat_trans.
  Defined.

  Definition free_algebra_form_adjunction
    : form_adjunction
        free_algebra_functor
        forgetful
        free_algebra_unit
        free_algebra_counit.
  Proof.
    split.
    - intros X.
      simpl.
      use (free_algebra_maps_eq (free_algebra_functor_obj X)).
      + apply free_inclusion.
      + cbn -[free_algebra_ump].
        intros x.
        unfold free_algebra_functor_mor.
        etrans.
        {
          apply maponpaths.
          apply (free_algebra_ump_commute
                   (free_to_sig_algebra
                      Σ
                      (free_carrier Σ X (free_alg X))
                      (free_alg (free_carrier Σ X (free_alg X))))).
        }
        unfold free_algebra_counit_data.
        etrans.
        {
          apply (free_algebra_ump_commute (free_algebra_functor_obj X)).
        }
        apply idpath.
      + intros a.
        apply idpath.
    - intros X ; cbn -[free_algebra_ump].
      use funextsec.
      intro x.
      unfold free_algebra_unit_data, free_algebra_counit_data.
      apply free_algebra_ump_commute.
  Qed.
  
  Definition free_algebra_are_adjoints
    : are_adjoints free_algebra_functor forgetful.
  Proof.
    use make_are_adjoints.
    - exact free_algebra_unit.
    - exact free_algebra_counit.
    - exact free_algebra_form_adjunction.
  Defined.

  Definition free_algebra_monad
    : Monad HSET
    := Monad_from_adjunction free_algebra_are_adjoints.
End FreeAlgebraAdj.

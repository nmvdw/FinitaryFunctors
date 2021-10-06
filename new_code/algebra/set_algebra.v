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

Local Open Scope container_scope.
Local Open Scope set.
Local Open Scope cat.

Definition interpret_container
           (C : container)
           (X : hSet)
  : hSet
  := ∑ (s : shapes C), funset (positions C s) X.

Notation "⟦ C ⟧ X" := (interpret_container C X) (at level 70) : container_scope.
(** \[[ and \]] *)

(** Relevant builders *)
Definition shape_of
           {C : container}
           {X : hSet}
           (x : ⟦ C ⟧ X)
  : shapes C
  := pr1 x.

Definition position_of
           {C : container}
           {X : hSet}
           (x : ⟦ C ⟧ X)
  : positions C (shape_of x) → X
  := pr2 x.

Definition cpair
           {C : container}
           {X : hSet}
           (s : shapes C)
           (f : positions C s → X)
  : ⟦ C ⟧ X
  := s ,, f.

(** The action on maps and the functor laws *)
Definition interpret_container_map
           (C : container)
           {X Y : hSet}
           (f : X → Y)
  : ⟦ C ⟧ X → ⟦ C ⟧ Y
  := λ x, cpair (shape_of x) (λ p, f (position_of x p)).

Definition container_to_functor_data
           (C : container)
  : functor_data HSET HSET.
Proof.
  use make_functor_data.
  - exact (λ Z, ⟦ C ⟧ Z).
  - exact (@interpret_container_map C).
Defined.

Definition container_is_functor
           (C : container)
  : is_functor (container_to_functor_data C).
Proof.
  split.
  - intros X.
    apply idpath.
  - intros X Y Z f g.
    apply idpath.
Qed.

Definition container_to_functor
           (C : container)
  : SET ⟶ SET.
Proof.
  use make_functor.
  - exact (container_to_functor_data C).
  - exact (container_is_functor C).
Defined.

(** The interpretations of the standard containers correspond with what's expected *)
Definition interpret_const_to_const
           {A : hSet}
           {X : hSet}
  : ⟦ A ⟧ X → A
  := λ x, shape_of x.

Definition const_to_interpret_const
           {A : hSet}
           {X : hSet}
  : A → ⟦ A ⟧ X
  := λ a, @cpair (constant_container _) _ a fromempty.

Definition interpret_const_to_const_to_interpret_const
           {A : hSet}
           {X : hSet}
           (x : ⟦ A ⟧ X)
  : const_to_interpret_const (interpret_const_to_const x) = x.
Proof.
  destruct x as [ s f ].
  unfold const_to_interpret_const, cpair ; cbn.
  apply maponpaths.
  use funextsec.
  intro z.
  destruct z.
Qed.

Definition const_to_interpret_const_to_const
           {A : hSet}
           {X : hSet}
           (a : A)
  : interpret_const_to_const (const_to_interpret_const a : ⟦ _ ⟧ X) = a.
Proof.
  apply idpath.
Qed.

Definition interpret_const
           (A : hSet)
           (X : hSet)
  : ⟦ A ⟧ X ≃ A.
Proof.
  use make_weq.
  - exact interpret_const_to_const.
  - use gradth.
    + exact const_to_interpret_const.
    + exact interpret_const_to_const_to_interpret_const.
    + exact const_to_interpret_const_to_const.
Defined.

Definition interpret_const_nat_trans
           (A : hSet)
  : container_to_functor A ⟹ constant_functor HSET HSET A.
Proof.
  use make_nat_trans.
  - exact (λ _, interpret_const_to_const).
  - abstract
      (intros X Y f ;
       apply idpath).
Defined.

Definition interpret_const_nat_iso
           (A : hSet)
  : nat_iso
      (container_to_functor A)
      (constant_functor HSET HSET A).
Proof.
  use make_nat_iso.
  - exact (interpret_const_nat_trans A).
  - intro X.
    exact (hset_equiv_is_iso _ _ (interpret_const A X)).
Defined.

Definition interpret_identity_to_identity
           {X : hSet}
  : ⟦ I ⟧ X → X
  := λ x, position_of x tt.

Definition identity_to_interpret_identity
           {X : hSet}
  : X → ⟦ I ⟧ X
  := λ x, @cpair identity_container _ tt (λ _, x).

Definition interpret_identity_to_identity_to_interpret_identity
           {X : hSet}
           (x : ⟦ I ⟧ X)
  : identity_to_interpret_identity (interpret_identity_to_identity x) = x.
Proof.
  destruct x as [ [ ] f ].
  unfold identity_to_interpret_identity ; cbn.
  apply maponpaths.
  use funextsec.
  intro z.
  destruct z.
  apply idpath.
Qed.

Definition identity_to_interpret_identity_to_identity
           {X : hSet}
           (x : X)
  : interpret_identity_to_identity (identity_to_interpret_identity x) = x.
Proof.
  apply idpath.
Qed.

Definition interpret_identity
           (X : hSet)
  : ⟦ I ⟧ X ≃ X.
Proof.
  use make_weq.
  - exact interpret_identity_to_identity.
  - use gradth.
    + exact identity_to_interpret_identity.
    + exact interpret_identity_to_identity_to_interpret_identity.
    + exact identity_to_interpret_identity_to_identity.
Defined.

Definition interpret_identity_nat_trans
  : container_to_functor I ⟹ functor_identity HSET.
Proof.
  use make_nat_trans.
  - exact @interpret_identity_to_identity.
  - abstract
      (intros X Y f ;
       apply idpath).
Defined.    

Definition interpret_identity_nat_iso
  : nat_iso
      (container_to_functor I)
      (functor_identity HSET).
Proof.
  use make_nat_iso.
  - exact interpret_identity_nat_trans.
  - intro X.
    exact (hset_equiv_is_iso _ _ (interpret_identity X)).
Defined.

Definition interpret_prod_to_prod
           {C₁ C₂ : container}
           {X : hSet}
  : ⟦ C₁ ⊗ C₂ ⟧ X → ⟦ C₁ ⟧ X × ⟦ C₂ ⟧ X
  := λ z, cpair (pr1 (shape_of z)) (λ p, position_of z (inl p))
          ,,
          cpair (pr2 (shape_of z)) (λ p, position_of z (inr p)).

Definition prod_to_interpret_prod
           {C₁ C₂ : container}
           {X : hSet}
  : ⟦ C₁ ⟧ X × ⟦ C₂ ⟧ X → ⟦ C₁ ⊗ C₂ ⟧ X
  := λ z, @cpair
            (prod_container _ _)
            _
            (shape_of (pr1 z) ,, shape_of (pr2 z))
            (coprod_rect _ (position_of (pr1 z)) (position_of (pr2 z))).

Definition interpret_prod_to_prod_to_interpret_prod
           {C₁ C₂ : container}
           {X : hSet}
           (x : ⟦ C₁ ⊗ C₂ ⟧ X)
  : prod_to_interpret_prod (interpret_prod_to_prod x) = x.
Proof.
  destruct x as [ [ s₁ s₂ ] f ].
  unfold interpret_prod_to_prod, prod_to_interpret_prod ; cbn.
  apply maponpaths.
  use funextsec.
  intro z.
  destruct z as [ z | z ].
  - apply idpath.
  - apply idpath.
Qed.

Definition prod_to_interpret_prod_to_prod
           {C₁ C₂ : container}
           {X : hSet}
           (x : ⟦ C₁ ⟧ X × ⟦ C₂ ⟧ X)
  : interpret_prod_to_prod (prod_to_interpret_prod x) = x.
Proof.
  apply idpath.
Qed.
  
Definition interpret_prod
           (C₁ C₂ : container)
           (X : hSet)
  : ⟦ C₁ ⊗ C₂ ⟧ X ≃ ⟦ C₁ ⟧ X × ⟦ C₂ ⟧ X.  
Proof.
  use make_weq.
  - exact interpret_prod_to_prod.
  - use gradth.
    + exact prod_to_interpret_prod.
    + exact interpret_prod_to_prod_to_interpret_prod.
    + exact prod_to_interpret_prod_to_prod.
Defined.

Definition interpret_prod_nat_trans
           (C₁ C₂ : container)
  : container_to_functor (C₁ ⊗ C₂)
    ⟹
    BinProduct_of_functors
      _ _
      BinProductsHSET
      (container_to_functor C₁)
      (container_to_functor C₂).
Proof.
  use make_nat_trans.
  - exact (@interpret_prod_to_prod C₁ C₂).
  - abstract
      (intros X Y f ;
       apply idpath).
Defined.
  
Definition interpret_prod_nat_iso
           (C₁ C₂ : container)
  : nat_iso
      (container_to_functor (C₁ ⊗ C₂))
      (BinProduct_of_functors
         _ _
         BinProductsHSET
         (container_to_functor C₁)
         (container_to_functor C₂)).
Proof.
  use make_nat_iso.
  - exact (interpret_prod_nat_trans C₁ C₂).
  - intro X.
    exact (hset_equiv_is_iso
             (⟦ C₁ ⊗ C₂ ⟧ X)
             (⟦ C₁ ⟧ X × ⟦ C₂ ⟧ X)
             (interpret_prod C₁ C₂ X)).
Defined.

Definition interpret_sum_to_sum
           {C₁ C₂ : container}
           {X : hSet}
  : ⟦ C₁ ⊕ C₂ ⟧ X → (⟦ C₁ ⟧ X) ⨿ (⟦ C₂ ⟧ X).
Proof.
  intros x.
  induction x as [x y].
  induction x as [x | x].
  - exact (inl (x ,, y)).
  - exact (inr (x ,, y)).
Defined.

Definition sum_to_interpret_sum
           {C₁ C₂ : container}
           {X : hSet}
  : (⟦ C₁ ⟧ X) ⨿ (⟦ C₂ ⟧ X) → ⟦ C₁ ⊕ C₂ ⟧ X.
Proof.
  intros x.
  induction x as [x | x].
  - induction x as [x y].
    exact (inl x ,, y).
  - induction x as [x y].
    exact (inr x ,, y).
Defined.

Definition sum_to_interpret_sum_to_sum
           {C₁ C₂ : container}
           {X : hSet}
           (x : (⟦ C₁ ⟧ X) ⨿ (⟦ C₂ ⟧ X))
  : interpret_sum_to_sum (sum_to_interpret_sum x) = x.
Proof.
  induction x as [x | x].
  - induction x as [x y].
    apply idpath.
  - induction x as [x y].
    apply idpath.
Qed.

Definition interpret_sum_to_sum_to_interpret_sum
           {C₁ C₂ : container}
           {X : hSet}
           (x : ⟦ C₁ ⊕ C₂ ⟧ X)
  : sum_to_interpret_sum (interpret_sum_to_sum x) = x.
Proof.
  induction x as [x y].
  induction x as [x | x].
  - apply idpath.
  - apply idpath.
Qed.

Definition interpret_sum
           {C₁ C₂ : container}
           (X : hSet)
  : ⟦ C₁ ⊕ C₂ ⟧ X ≃ (⟦ C₁ ⟧ X) ⨿ (⟦ C₂ ⟧ X).
Proof.
  use make_weq.
  - exact interpret_sum_to_sum.
  - use gradth.
    + exact sum_to_interpret_sum.
    + exact interpret_sum_to_sum_to_interpret_sum.
    + exact sum_to_interpret_sum_to_sum.
Defined.


Definition interpret_sum_nat_trans
           (C₁ C₂ : container)
  : container_to_functor (C₁ ⊕ C₂)
    ⟹
    BinCoproduct_of_functors
      _ _
      BinCoproductsHSET
      (container_to_functor C₁)
      (container_to_functor C₂).
Proof.
  use make_nat_trans.
  - exact (@interpret_sum_to_sum _ _).
  - abstract
      (intros x y f ;
       use funextsec ;
       intros z ;
       induction z as [z₁ z₂] ;
       induction z₁ ; cbn ; apply idpath).
Defined.    

Definition interpret_sum_nat_iso
           (C₁ C₂ : container)
  : nat_iso
      (container_to_functor (C₁ ⊕ C₂))
      (BinCoproduct_of_functors
         _ _
         BinCoproductsHSET
         (container_to_functor C₁)
         (container_to_functor C₂)).
Proof.
  use make_nat_iso.
  - exact (interpret_sum_nat_trans C₁ C₂).
  - intro X.
    exact (hset_equiv_is_iso
             (⟦ C₁ ⊕ C₂ ⟧ X)
             (setcoprod (⟦ C₁ ⟧ X) (⟦ C₂ ⟧ X))
             (interpret_sum X)).
Defined.
    
(* Interpretation of exponentials *)
Definition container_exp_functor
           (A : hSet)
           (F : HSET ⟶ HSET)
  : HSET ⟶ HSET
  := F ∙ exponential_functor A.

Definition interpret_exp_to_exp
           {C : container}
           {A X : hSet}
  : ⟦ C ^ A ⟧ X → (A → ⟦ C ⟧ X).
Proof.
  intros f a.
  refine (pr1 f a ,, _).
  exact (λ p, pr2 f (a ,, p)).
Defined.

Definition exp_to_interpret_exp
           {C : container}
           {A X : hSet}
  : (A → ⟦ C ⟧ X) → ⟦ C ^ A ⟧ X.
Proof.
  intros f.
  simple refine (_ ,, _).
  - exact (λ a, pr1 (f a)).
  - exact (λ x, pr2 (f (pr1 x)) (pr2 x)).
Defined.

Definition exp_to_interpret_exp_to_exp
           {C : container}
           {A X : hSet}
           (f : A → ⟦ C ⟧ X)
  : interpret_exp_to_exp (exp_to_interpret_exp f) = f.
Proof.
  apply idpath.
Qed.

Definition interpret_exp_to_exp_to_interpret_exp
           {C : container}
           {A X : hSet}
           (x : ⟦ C ^ A ⟧ X)
  : exp_to_interpret_exp (interpret_exp_to_exp x) = x.
Proof.
  apply idpath.
Qed.

Definition interpret_exp
           {C : container}
           {A : hSet}
           (X : hSet)
  : ⟦ C ^ A ⟧ X ≃ (A → ⟦ C ⟧ X).
Proof.
  use make_weq.
  - exact interpret_exp_to_exp.
  - use gradth.
    + exact exp_to_interpret_exp.
    + exact interpret_exp_to_exp_to_interpret_exp.
    + exact exp_to_interpret_exp_to_exp.
Defined.

Definition interpret_exp_nat_trans
           (C : container)
           (A : hSet)
  : container_to_functor (C ^ A)
    ⟹
    container_exp_functor A (container_to_functor C).
Proof.
  use make_nat_trans.
  - exact (@interpret_exp_to_exp C A).
  - abstract
      (intros X Y f ; cbn ;
       apply idpath).
Defined.  

Definition interpret_exp_nat_iso
           (C : container)
           (A : hSet)
  : nat_iso
      (container_to_functor (C ^ A))
      (container_exp_functor A (container_to_functor C)).
Proof.
  use make_nat_iso.
  - exact (interpret_exp_nat_trans C A).
  - intro X.
    exact (hset_equiv_is_iso
             (⟦ C ^ A ⟧ X)
             (funset A (⟦ C ⟧ X))
             (interpret_exp X)).
Defined.

Definition sem_endpoint
           {P : container}
           {X : hSet}
           {Q : hSet}
           (c : ⟦ P ⟧ X → X)
           (var : Q → X)
           (x : W P Q)
  : X.
Proof.
  induction x as [ v | s p IHp ].
  - exact (var v).
  - exact (c (s ,, IHp)).
Defined.

(*
Definition test
           (Q : hSet)
  : functor SET SET.
Proof.
  use make_functor.
  - use make_functor_data.
    + exact (λ X, funset Q X).
    + cbn ; intros ? ? f.
      intros g q.
      exact (f (g q)).
  - repeat split.
Defined.      

Definition sem_endpoint_nat_trans
           {P : container}
           {X : hSet}
           {Q : hSet}
           (c : ⟦ P ⟧ X → X)
           (x : W P Q)
  : nat_trans
      (test Q)
      (functor_identity _).
Proof.
  use make_nat_trans.
  - intros ? v.
    cbn in v.
    exact (sem_endpoint c v x).
*)

(*
Definition sem_endpoint
           {Σ : hit_signature}
           {X : hSet}
           (c : ⟦ point_constr Σ ⟧ X → X)
           (i : path_index Σ)
           (var : path_arg Σ i → X)
           (x : W (point_constr Σ) (path_arg Σ i))
  : X.
Proof.
  induction x as [ v | s p IHp ].
  - exact (var v).
  - exact (c (s ,, IHp)).
Defined.
 *)

Close Scope set.

Definition hit_prealgebra
           (Σ : hit_signature)
  : category
  := total_category
       (fun_algebra_disp_cat
          (container_to_functor (point_constr Σ))).

Section Accessors.
  Context {Σ : hit_signature}
          (X : hit_prealgebra Σ).

  Definition alg_carrier : hSet
    := pr1 X.

  Definition algebra_map
    : ⟦ point_constr Σ ⟧ alg_carrier → alg_carrier
    := pr2 X.
End Accessors.

Definition make_hit_prealgebra
           {Σ : hit_signature}
           (X : hSet)
           (f : ⟦ point_constr Σ ⟧ X → X)
  : hit_prealgebra Σ
  := X ,, f.

Definition is_hit_algebra
           {Σ : hit_signature}
           (X : hit_prealgebra Σ)
  : UU
  := ∏ (i : path_index Σ)
       (p : path_arg Σ i → alg_carrier X),
     sem_endpoint (algebra_map X) p (path_lhs Σ i)
     =
     sem_endpoint (algebra_map X) p (path_rhs Σ i).

Definition hit_algebra_disp_cat
           (Σ : hit_signature)
  : disp_cat (hit_prealgebra Σ)
  := disp_full_sub _ is_hit_algebra.

Definition hit_algebra
           (Σ : hit_signature)
  : category
  := total_category (hit_algebra_disp_cat Σ).

Definition hit_algebra_map_eq
           {Σ : hit_signature}
           {X Y : hit_algebra Σ}
           {f g : X --> Y}
           (p : ∏ x, pr11 f x = pr11 g x)
  : f = g.
Proof.
  use subtypePath.
  {
    intro ; apply isapropunit.
  }
  use subtypePath.
  {
    intro ; apply homset_property.
  }
  use funextsec.
  exact p.
Qed.

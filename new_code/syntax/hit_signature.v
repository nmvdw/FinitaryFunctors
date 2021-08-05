Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.FiniteSets.

(** Here we define signatures for HITs *)
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

(*
Local Open Scope cat.

Declare Scope container_scope.

(** The empty hSet *)
Definition emptyset
  : hSet
  := make_hSet empty isasetempty.

(** Containers *)
Definition container
  := ∑ (A : hSet), A → hSet.

(** Projections and builders *)
Definition shapes
           (C : container)
  : hSet
  := pr1 C.

Definition positions
           (C : container)
           (s : shapes C)
  : hSet
  := pr2 C s.

Definition make_container
           (shapes : hSet)
           (positions : shapes → hSet)
  : container
  := shapes ,, positions.

Notation "S ◅ P" := (make_container S P) (at level 60) : container_scope. (* \tw5 *)

Local Open Scope set.
Local Open Scope container_scope.

(** Some standard containers *)
Definition constant_container
           (A : hSet)
  : container
  := A ◅ (λ _, emptyset).

Coercion constant_container : hSet >-> container.

Definition identity_container
  : container
  := unitset ◅ (λ _, unitset).

Notation "'I'" := identity_container : container_scope.

Definition sum_container
           (C₁ C₂ : container)
  : container
  := (setcoprod (shapes C₁) (shapes C₂)) ◅ (coprod_rect _ (positions C₁) ((positions C₂))).

Notation "C₁ ⊕ C₂" := (sum_container C₁ C₂) : container_scope.

Definition prod_container
           (C₁ C₂ : container)
  : container
  := (shapes C₁ × shapes C₂) ◅ (λ z, setcoprod (positions C₁ (pr1 z)) (positions C₂ (pr2 z))).

Notation "C₁ ⊗ C₂" := (prod_container C₁ C₂) : container_scope.

Definition exp_container
           (A : hSet)
           (C : container)
  : container
  := (funset A (shapes C)) ◅ (λ f, ∑ (a : A), positions C (f a)).

Notation "C ^ A" := (exp_container A C) : container_scope.

(** Interpretations of containers as functors *)
Definition interpret_container
           (C : container)
           (X : hSet)
  : hSet
  := ∑ (s : shapes C), funset (positions C s) X.

Notation "⟦ C ⟧ X" := (interpret_container C X) (at level 70) : container_scope. (** \[[ and \]] *)

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

Definition interpret_container_map_id
           (C : container)
           (X : hSet)
  : interpret_container_map C (idfun X) = idfun _.
Proof.
  apply idpath.
Qed.

Definition interpret_container_map_comp
           (C : container)
           {X Y Z : hSet}
           (f : X → Y)
           (g : Y → Z)
  : (interpret_container_map C (g ∘ f)
     =
     interpret_container_map C g ∘ interpret_container_map C f)%functions.
Proof.
  apply idpath.
Qed.

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
    apply interpret_container_map_id.
  - intros X Y Z f g.
    apply interpret_container_map_comp.
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

(*
- Morphisms of containers
- Functor from the category of containers to endofunctors on hSet
 *)

(** Finitary containers *)
Definition is_finitary
           (C : container)
  : hProp
  := forall_hProp (λ s, isfinite (positions C s)).

(** Examples of finitary containers *)
Definition is_finitary_constant_container
           (A : hSet)
  : is_finitary A.
Proof.
  intro s.
  apply isfiniteempty.
Qed.

Definition is_finitary_identity_container
  : is_finitary I.
Proof.
  intro s.
  apply isfiniteunit.
Qed.

Definition is_finitary_sum_container
           {C₁ C₂ : container}
           (H₁ : is_finitary C₁)
           (H₂ : is_finitary C₂)
  : is_finitary (C₁ ⊕ C₂).
Proof.
  intro s.
  destruct s.
  - exact (H₁ p).
  - exact (H₂ p).
Qed.

Definition is_finitary_prod_container
           {C₁ C₂ : container}
           (H₁ : is_finitary C₁)
           (H₂ : is_finitary C₂)
  : is_finitary (C₁ ⊗ C₂).
Proof.
  intro s.
  apply isfinitecoprod.
  - exact (H₁ (pr1 s)).
  - exact (H₂ (pr2 s)).
Qed.

Definition is_finitary_exp_container
           {A : hSet}
           (HA : isfinite A)
           {C : container}
           (HC : is_finitary C)
  : is_finitary (C ^ A).
Proof.
  intro s.
  apply isfinitetotal2.
  - exact HA.
  - intro x.
    exact (HC (s x)).
Qed.

(** W-types with variables *)
Inductive W (C : container) (X : hSet) : UU :=
| var : X → W C X
| sup : ∏ (s : shapes C), (positions C s → W C X) → W C X.

Arguments var {_ _} _.
Arguments sup {_ _} _ _.

(* To prove that W is a set, use encode decode *)
Definition path_sup
           {C : container}
           {X : hSet}
           {s₁ s₂ : shapes C}
           (p : s₁ = s₂)
           {φ : positions C s₁ → W C X}
           {ψ : positions C s₂ → W C X}
           (q : ∏ (z : positions C s₁), φ z = ψ (transportf (positions C) p z))
  : sup s₁ φ = sup s₂ ψ.
Proof.
  induction p.
  apply maponpaths.
  exact (invmap (weqtoforallpaths _ φ ψ) (λ p, q p)).
Defined.
           
Fixpoint W_fam
         {C : container}
         {X : hSet}
         (x y : W C X)
  : UU
  := match x , y with
     | var x , var y => x = y
     | var _ , sup _ _ => ∅
     | sup _ _ , var _ => ∅
     | sup s φ , sup t ψ =>
       (∑ (q : s = t),
        ∏ (p : positions C s),
        W_fam (φ p) (ψ (transportf (positions C) q p)))%type
     end.

Definition W_fam_isaprop
           {C : container}
           {X : hSet}
           (x y : W C X)
  : isaprop (W_fam x y).
Proof.
  revert y.
  induction x as [ x | s φ IHφ ]
  ; intro y
  ; induction y as [ y | t ψ ].
  - apply X.
  - apply isapropempty.
  - apply isapropempty.
  - simpl.
    use isaproptotal2.
    + intro.
      apply impred ; intro.
      apply IHφ.
    + simpl.
      intros.
      apply (shapes C).
Qed.

Definition W_fam_refl
           {C : container}
           {X : hSet}
           (x : W C X)
  : W_fam x x.
Proof.
  induction x as [ x | s φ IHφ ] ; simpl.
  - apply idpath.
  - simple refine (idpath _ ,, _) ; cbn.
    intro.
    apply IHφ.
Defined.

Definition eq_to_W_fam
           {C : container}
           {X : hSet}
           {x y : W C X}
           (p : x = y)
  : W_fam x y.
Proof.
  induction p.
  exact (W_fam_refl _).
Defined.

Definition W_fam_to_eq
           {C : container}
           {X : hSet}
           {x y : W C X}
           (p : W_fam x y)
  : x = y.
Proof.
  revert y p.
  induction x as [ x | s φ IHφ ]
  ; intro y
  ; induction y as [ y | t ψ ]
  ; intro p
  ; cbn in p.
  - apply maponpaths.
    exact p.
  - induction p.
  - induction p.
  - induction p as [p₁ p₂].
    use path_sup.
    + exact p₁.
    + induction p₁.
      cbn ; cbn in p₂.
      intro z.
      apply IHφ.
      apply p₂.
Defined.

Definition W_fam_to_eq_to_W_fam
           {C : container}
           {X : hSet}
           {x y : W C X}
           (p : W_fam x y)
  : eq_to_W_fam (W_fam_to_eq p) = p.
Proof.
  apply W_fam_isaprop.
Qed.

Definition eq_to_W_fam_to_eq_to_W_fam
           {C : container}
           {X : hSet}
           {x y : W C X}
           (p : x = y)
  : W_fam_to_eq (eq_to_W_fam p) = p.
Proof.
  induction p.
  induction x as [ x | s φ IHφ ] ; simpl.
  - apply idpath.
  - cbn in IHφ.
    refine (_ @ maponpaths_idpath).
    apply maponpaths.
    refine (_ @ homotinvweqweq
                  (weqtoforallpaths _ φ φ)
                  _).
    apply maponpaths.
    use funextsec.
    intro z.
    apply IHφ.
Qed.

Definition W_fam_equiv
           {C : container}
           {X : hSet}
           (x y : W C X)
  : W_fam x y ≃ x = y.
Proof.
  use make_weq.
  - exact W_fam_to_eq.
  - use gradth.
    + exact eq_to_W_fam.
    + exact W_fam_to_eq_to_W_fam.
    + exact eq_to_W_fam_to_eq_to_W_fam.
Defined.

Definition isaset_W
           (C : container)
           (X : hSet)
  : isaset (W C X).
Proof.
  intros x y.
  refine (isofhlevelweqf 1 (W_fam_equiv _ _) _).
  apply W_fam_isaprop.
Qed.

Definition W_hSet
           (C : container)
           (X : hSet)
  : hSet.
Proof.
  use make_hSet.
  - exact (W C X).
  - apply isaset_W.
Defined.

(** W C is a functor *)
Definition W_on_mor
           (C : container)
           {X Y : hSet}
           (f : X → Y)
  : W C X → W C Y.
Proof.
  intro x.
  induction x as [ x | s φs IHφs ].
  - exact (var (f x)).
  - exact (sup s (λ p, IHφs p)).
Defined.

Definition W_on_id
           (C : container)
           (X : hSet)
  : W_on_mor C (idfun X) = idfun _.
Proof.
  use funextsec.
  intro x ; cbn.
  induction x as [ x | s φs IHφs ] ; simpl.
  - apply idpath.
  - apply maponpaths.
    use funextsec.
    intro.
    apply IHφs.
Qed.

Definition W_on_comp
           (C : container)
           {X Y Z : hSet}
           (f : X → Y)
           (g : Y → Z)
  : (W_on_mor C (g ∘ f)
     =
     W_on_mor C g ∘ W_on_mor C f)%functions.
Proof.
  use funextsec.
  intro x ; cbn.
  induction x as [ x | s φs IHφs ] ; simpl.
  - apply idpath.
  - apply maponpaths.
    use funextsec.
    intro.
    apply IHφs.
Qed.

Definition W_functor_data
           (C : container)
  : functor_data HSET HSET.
Proof.
  use make_functor_data.
  - exact (λ X, W_hSet C X).
  - exact (@W_on_mor C).
Defined.

Definition W_is_functor
           (C : container)
  : is_functor (W_functor_data C).
Proof.
  split ; intro ; intros.
  - apply W_on_id.
  - apply W_on_comp.
Defined.

Definition W_functor
           (C : container)
  : HSET ⟶ HSET.
Proof.
  use make_functor.
  - exact (W_functor_data C).
  - exact (W_is_functor C).
Defined.

Close Scope set.
*)

Definition hit_signature
  : UU
  := ∑ (point_constr : container)
       (path_arg : container),
     ∏ (s : shapes path_arg),
       W point_constr (positions path_arg s)
       ×
       W point_constr (positions path_arg s).

(*
nattrans

W C X
≃
y X ⇒ (X → W C X)

∏ (s : shapes path_arg), W point_constr (positions path_arg s)
≃
∏ (s : shapes path_arg),
  nattrans (yoneda (positions path_arg s)) (W point_constr)
 *)

Definition point_constr
           (Σ : hit_signature)
  : container
  := pr1 Σ.

Definition path_index
           (Σ : hit_signature)
  : hSet
  := shapes (pr12 Σ).

Definition path_arg
           (Σ : hit_signature)
           (s : path_index Σ)
  : hSet
  := positions (pr12 Σ) s.

Definition path_lhs
           (Σ : hit_signature)
           (s : path_index Σ)
  : W (point_constr Σ) (path_arg Σ s)
  := pr1 (pr22 Σ s).

Definition path_rhs
           (Σ : hit_signature)
           (s : path_index Σ)
  : W (point_constr Σ) (path_arg Σ s)
  := pr2 (pr22 Σ s).

Definition make_hit_signature
           (point_constr : container)
           (path_arg : container)
           (path_lhs : ∏ (s : shapes path_arg),
                       W point_constr (positions path_arg s))
           (path_rhs : ∏ (s : shapes path_arg),
                       W point_constr (positions path_arg s))
  : hit_signature
  := point_constr ,, (path_arg ,, λ s, path_lhs s ,, path_rhs s).

Definition is_finitary_hit
           (Σ : hit_signature)
  : UU
  := is_finitary (point_constr Σ) × is_finitary (pr12 Σ).

(* Algebras *)
Definition fun_algebra_disp_cat
           {C : category}
           (F : C ⟶ C)
  : disp_cat C.
Proof.
  use disp_struct.
  - exact (λ x, F x --> x).
  - exact (λ x y hx hy f, hx · f = #F f · hy).
  - abstract
      (simpl ;
       intros ; 
       apply C).
  - abstract
      (simpl ;
       intros ;
       rewrite functor_id, id_left, id_right ;
       apply idpath).
  - abstract
      (simpl ;
       intros ? ? ? ? ? ? ? ? p q ;
       rewrite assoc ;
       rewrite p ;
       rewrite assoc' ;
       rewrite q ;
       rewrite assoc ;
       apply maponpaths_2 ;
       rewrite functor_comp ;
       apply idpath).
Defined.


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

Definition hit_algebra_disp_cat
           (Σ : hit_signature)
  : disp_cat
      (total_category
         (fun_algebra_disp_cat
            (container_to_functor (point_constr Σ)))).
Proof.
  use disp_full_sub.
  intros X.
  induction X as [X c] ; simpl in *.
  exact (∏ (i : path_index Σ)
           (p : path_arg Σ i → X),
         sem_endpoint c i p (path_lhs Σ i)
         =
         sem_endpoint c i p (path_rhs Σ i)).
Defined.

Definition hit_algebra
           (Σ : hit_signature)
  : category
  := total_category (hit_algebra_disp_cat Σ).


Definition nat_container
  : container
  := unitset ⊕ I.

Definition bintree_container
  : container
  := unitset ⊕ I ⊗ I.

(**
Natural numbers modulo 2

Inductive ℕ₂ : Type :=
| 0 : ℕ₂
| S : ℕ₂ → ℕ₂
| mod : ∏ (n : ℕ₂), S(S n) = n
 *)
Definition mod2_point_constr
  : container.
Proof.
  use make_container.
  - exact boolset.
  - intro b.
    destruct b.
    + exact emptyset.
    + exact unitset.
Defined.

Definition mod2_path_arg
  : container.
Proof.
  use make_container.
  - exact unitset.
  - exact (λ _, unitset).
Defined.

Definition mod2 : hit_signature.
Proof.
  use make_hit_signature.
  - exact mod2_point_constr.
  - exact mod2_path_arg.
  - intro x ; simpl in *.
    use sup.
    + apply false.
    + simpl.
      intro.
      use sup.
      * apply false.
      * apply var.
  - intro x ; simpl in *.
    apply var.
    exact x.
Defined.

Definition is_finitary_mod2
  : is_finitary_hit mod2.
Proof.
  split.
  - intro x.
    destruct x ; cbn -[isfinite].
    + apply isfiniteempty.
    + apply isfiniteunit.
  - intro.
    apply isfiniteunit.
Qed.

Section Mod2Algebra.
  Variable (X : hit_algebra mod2).

  Definition mod2_carrier
    : hSet
    := pr11 X.

  Definition mod2_Z
    : mod2_carrier.
  Proof.
    pose (pr21 X) as f.
    cbn in f.
    apply f.
    simple refine (true ,, fromempty).
  Defined.

  Definition mod2_S
    : mod2_carrier → mod2_carrier.
  Proof.
    pose (pr21 X) as f.
    cbn in f.
    intro x.
    apply f.
    exact (false ,, (λ _, x)).
  Defined.

  Definition mod2_path
    : ∏ (n : mod2_carrier), mod2_S (mod2_S n) = n.
  Proof.
    pose (pr2 X) as p.
    cbn in p.
    intro n.
    exact (p tt (λ _ , n)).
  Defined.
End Mod2Algebra.

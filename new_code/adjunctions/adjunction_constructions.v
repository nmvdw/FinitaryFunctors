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
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.
Require Import UniMath.CategoryTheory.Adjunctions.Core.

Require Import prelude.

Open Scope cat.

(**
For this, we use a general method to construct functors between categories of algebras.
We need a natural transformation witnessing commutation.
 *)
Section AlgebraFunctor.
  Context {C D : category}
          (A₁ : C ⟶ C)
          (A₂ : D ⟶ D)
          (F : C ⟶ D)
          (n : F ∙ A₂ ⟹ A₁ ∙ F).

  Definition fun_algebra_disp_functor_data
    : disp_functor_data
        F
        (fun_algebra_disp_cat A₁)
        (fun_algebra_disp_cat A₂).
  Proof.
    simple refine (_ ,, _) ; cbn.
    - exact (λ x f, n x · #F f).
    - abstract
        (simpl ;
         intros x y hx hy f p ;
         rewrite !assoc' ;
         rewrite <- functor_comp ;
         rewrite p ;
         rewrite functor_comp ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         exact (!(nat_trans_ax n _ _ f))).
  Defined.

  Definition fun_algebra_disp_functor_axioms
    : disp_functor_axioms fun_algebra_disp_functor_data.
  Proof.
    split ; intros ; apply D.
  Qed.
  
  Definition fun_algebra_disp_functor
    : disp_functor
        F
        (fun_algebra_disp_cat A₁)
        (fun_algebra_disp_cat A₂).
  Proof.
    simple refine (_ ,, _).
    - exact fun_algebra_disp_functor_data.
    - exact fun_algebra_disp_functor_axioms.
  Defined.
End AlgebraFunctor.

(**
Here we give how a condition to show a natural transformation is an algebra morphism at each coodinate.
 *)
Section AlgebraNatTrans.
  Context {C D : category}
          {F G : C ⟶ D}
          (A₁ : C ⟶ C)
          (A₂ : D ⟶ D)
          (η : F ⟹ G)
          (FF : disp_functor
                  F
                  (fun_algebra_disp_cat A₁)
                  (fun_algebra_disp_cat A₂))
          (GG : disp_functor
                  G
                  (fun_algebra_disp_cat A₁)
                  (fun_algebra_disp_cat A₂))
          (p : ∏ (x : C) (hx : A₁ x --> x),
               FF x hx · η x = # A₂ (η x) · GG x hx).

  Definition fun_algebra_disp_nat_trans_data
    : disp_nat_trans_data η FF GG.
  Proof.
    exact p.
  Defined.

  Definition fun_algebra_disp_nat_trans_axioms
    : disp_nat_trans_axioms fun_algebra_disp_nat_trans_data.
  Proof.
    intros x y f hx hy hf.
    apply D.
  Qed.

  Definition fun_algebra_disp_nat_trans
    : disp_nat_trans η FF GG.
  Proof.
    simple refine (_ ,, _).
    - exact fun_algebra_disp_nat_trans_data.
    - exact fun_algebra_disp_nat_trans_axioms.
  Defined.
End AlgebraNatTrans.

Section AlgebraAdjunction.
  Context {C D : category}
          (A₁ : C ⟶ C)
          (A₂ : D ⟶ D)
          (adj : adjunction C D).

  Local Notation "'L'" := (left_functor adj).
  Local Notation "'R'" := (right_functor adj).

  Local Notation η := (unit_from_are_adjoints adj).
  Local Notation ε := (counit_from_are_adjoints adj).

  Variable (nL : L ∙ A₂ ⟹ A₁ ∙ L)
           (nR : R ∙ A₁ ⟹ A₂ ∙ R)
           (H₁ : ∏ (X : D), nL (R X) · #L (nR X) · ε (A₂ X) = # A₂ (ε X))
           (H₂ : ∏ (X : C), η (A₁ X) = # A₁ (η X) · nR (L X) · #R (nL X)).

  Definition fun_algebra_disp_adjunction_data
    : disp_adjunction_data
        adj
        (fun_algebra_disp_cat A₁)
        (fun_algebra_disp_cat A₂).
  Proof.
    simple refine (_ ,, (_ ,, (_ ,, _))).
    - exact (fun_algebra_disp_functor _ _ _ nL).
    - exact (fun_algebra_disp_functor _ _ _ nR).
    - abstract
        (refine (fun_algebra_disp_nat_trans _ _ _ _ _ _) ;
         intros x hx ;
         refine (nat_trans_ax η _ _ hx @ _) ; cbn ;
         rewrite !assoc ;
         rewrite functor_comp ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         apply H₂).
    - abstract
        (refine (fun_algebra_disp_nat_trans _ _ _ _ _ _) ;
         intros x hx ; cbn ;
         rewrite functor_comp ;
         rewrite !assoc' ;
         refine (maponpaths (λ z, _ · (_ · z)) (nat_trans_ax ε _ _ hx) @ _) ;
         cbn ;
         rewrite !assoc ;
         apply maponpaths_2 ;
         apply H₁).
  Defined.

  Definition fun_algebra_disp_adjunction
    : disp_adjunction
        adj
        (fun_algebra_disp_cat A₁)
        (fun_algebra_disp_cat A₂).
  Proof.
    simple refine (_ ,, _).
    - exact fun_algebra_disp_adjunction_data.
    - abstract
        (split ;
         [ intro ; intros ; apply D
         | intro ; intros ; apply C ]).
  Defined.
End AlgebraAdjunction.

Section DispFullSubFunctor.
  Context {C D : category}
          (P : C → UU)
          (Q : D → UU)
          (F : C ⟶ D)
          (H : ∏ (x : C), P x → Q(F x)).

  Definition disp_full_sub_functor_data
    : disp_functor_data F (disp_full_sub _ P) (disp_full_sub _ Q).
  Proof.
    simple refine (_ ,, _).
    - exact H.
    - exact (λ _ _ _ _ _ _, tt).
  Defined.

  Definition disp_full_sub_functor_axioms
    : disp_functor_axioms disp_full_sub_functor_data.
  Proof.
    split ; intros ; apply isapropunit.
  Qed.
  
  Definition disp_full_sub_functor
    : disp_functor F (disp_full_sub _ P) (disp_full_sub _ Q).
  Proof.
    simple refine (_ ,, _).
    - exact disp_full_sub_functor_data.
    - exact disp_full_sub_functor_axioms.
  Defined.
End DispFullSubFunctor.

Definition disp_full_sub_nat_trans
           {C D : category}
           (P : C → UU)
           (Q : D → UU)
           {F G : C ⟶ D}
           (η : F ⟹ G)
           (FF : disp_functor F (disp_full_sub _ P) (disp_full_sub _ Q))
           (GG : disp_functor G (disp_full_sub _ P) (disp_full_sub _ Q))
  : disp_nat_trans η FF GG.
Proof.
  simple refine ((λ _ _, tt) ,, _).
  abstract
    (intros x y f xx yy ff ; apply isapropunit).
Defined.

Section DispFullSubAdjunction.
  Context {C D : category}
          (adj : adjunction C D).

  Local Notation "'L'" := (left_functor adj).
  Local Notation "'R'" := (right_functor adj).

  Local Notation η := (unit_from_are_adjoints adj).
  Local Notation ε := (counit_from_are_adjoints adj).

  Variable (P : C → UU)
           (Q : D → UU)
           (H₁ : ∏ (x : C), P x → Q(L x))
           (H₂ : ∏ (x : D), Q x → P(R x)).

  Definition disp_full_sub_adjunction_data
    : disp_adjunction_data adj (disp_full_sub _ P) (disp_full_sub _ Q).
  Proof.
    simple refine (_ ,, (_ ,, (_ ,, _))).
    - exact (disp_full_sub_functor _ _ _ H₁).
    - exact (disp_full_sub_functor _ _ _ H₂).
    - apply disp_full_sub_nat_trans.
    - apply disp_full_sub_nat_trans.
  Defined.
  
  Definition disp_full_sub_adjunction
    : disp_adjunction adj (disp_full_sub _ P) (disp_full_sub _ Q).
  Proof.
    simple refine (_ ,, _).
    - exact disp_full_sub_adjunction_data.
    - abstract
        (split ; intro ; intros ; apply isapropunit).
  Defined.
End DispFullSubAdjunction.

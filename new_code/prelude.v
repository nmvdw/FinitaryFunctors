(** Here we define signatures for HITs *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.

Local Open Scope cat.

(** The empty hSet *)
Definition emptyset
  : hSet
  := make_hSet empty isasetempty.

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

Section TotalAdjunction.
  Context {C₁ C₂ : category}
          {D₁ : disp_cat C₁}
          {D₂ : disp_cat C₂}
          {adj : adjunction C₁ C₂}
          (disp_adj : disp_adjunction adj D₁ D₂).

  Local Notation L := (left_functor adj).
  Local Notation R := (right_functor adj).
  Local Notation η := (unit_from_are_adjoints adj).
  Local Notation ε := (counit_from_are_adjoints adj).

  Local Notation LL := (left_adj_over disp_adj).
  Local Notation RR := (right_adj_over disp_adj).
  Local Notation ηη := (unit_over disp_adj).
  Local Notation εε := (counit_over disp_adj).

  Definition total_unit_data
    : nat_trans_data
        (functor_identity (total_category D₁))
        (total_functor LL ∙ total_functor RR)
    := λ x, η (pr1 x) ,, ηη (pr1 x) (pr2 x).

  Definition total_unit_is_nat_trans
    : is_nat_trans _ _ total_unit_data.
  Proof.
    intros x y f.
    use total2_paths_f ; cbn.
    - exact (nat_trans_ax η _ _ (pr1 f)).
    - use transportf_transpose_left.
      exact (disp_nat_trans_ax ηη (pr2 f)).
  Qed.
    
  Definition total_unit
    : functor_identity (total_category D₁)
      ⟹
      total_functor LL ∙ total_functor RR.
  Proof.
    use make_nat_trans.
    - exact total_unit_data.
    - exact total_unit_is_nat_trans.
  Defined.
  
  Definition total_counit_data
    : nat_trans_data
        (total_functor RR ∙ total_functor LL)
        (functor_identity (total_category D₂))
    := λ x, ε (pr1 x) ,, εε (pr1 x) (pr2 x).

  Definition total_counit_is_nat_trans
    : is_nat_trans _ _ total_counit_data.
  Proof.
    intros x y f.
    use total2_paths_f ; cbn.
    - exact (nat_trans_ax ε _ _ (pr1 f)).
    - use transportf_transpose_left.
      exact (disp_nat_trans_ax εε (pr2 f)).
  Qed.
    
  Definition total_counit
    : total_functor RR ∙ total_functor LL
      ⟹
      functor_identity (total_category D₂).
  Proof.
    use make_nat_trans.
    - exact total_counit_data.
    - exact total_counit_is_nat_trans.
  Defined.

  Definition total_adjunction_data           
    : adjunction_data (total_category D₁) (total_category D₂).
  Proof.
    refine (total_functor (left_adj_over disp_adj) ,, _).
    refine (total_functor (right_adj_over disp_adj) ,, _).
    exact (total_unit ,, total_counit).
  Defined.

  Definition total_adjunction_form_adjunction
    : form_adjunction' total_adjunction_data.
  Proof.
    split.
    - intros x.
      use total2_paths_f ; cbn.
      + exact (pr12 adj (pr1 x)).
      + use transportf_transpose_left.
        exact (pr12 disp_adj _ (pr2 x)).
    - intros x.
      use total2_paths_f ; cbn.
      + exact (pr22 adj (pr1 x)).
      + use transportf_transpose_left.
        exact (pr22 disp_adj _ (pr2 x)).
  Qed.

  Definition total_adjunction
    : adjunction (total_category D₁) (total_category D₂)
    := total_adjunction_data ,, total_adjunction_form_adjunction.
End TotalAdjunction.

Local Open Scope stn.

Definition axiom_finite_choice
           {X : UU}
           (HX : isfinite X)
           (Y : X → UU)
           (f : ∏ (x : X), ∥ Y x ∥)
  : ∥ ∏ (x : X), Y x ∥.
Proof.
  unfold isfinite in HX.
  use (squash_to_prop HX) ; clear HX.
  {
    apply ishinh.
  }
  intros HX.
  destruct HX as [ n e ] ; unfold nelstruct in e.
  revert X Y f e.
  induction n as [ | n IHn ] ; intros X Y f e.
  - apply hinhpr.
    exact (λ x, fromempty (weqstn0toempty (invmap e x))).
  - pose (weqfromcoprodofstn 1 n) as w ; simpl in w.
    specialize (IHn (⟦ n ⟧)
                    (λ x, Y (e (w (inr x))))
                    (λ x, f (e (w (inr x)))) (idweq _)).
    use (squash_to_prop IHn) ; clear IHn.
    {
      apply ishinh.
    }
    intros IHn ; simpl in IHn.
    pose (q := f (e (weqfromcoprodofstn_map 1 n (inl (invmap weqstn1tounit tt))))).
    use (squash_to_prop q) ; clear q.
    {
      apply ishinh.
    }
    intro q.
    apply hinhpr.
    intros x.
    refine (transportf Y (homotweqinvweq (e ∘ w)%weq x) _) ; simpl.
    generalize (invmap (e ∘ w)%weq x).
    intro z.
    induction z as [ z | z ].
    + pose (p := homotinvweqweq weqstn1tounit z).
      assert (weqstn1tounit z = tt) as p'.
      {
        apply isapropunit.
      }
      induction p.
      induction p'.
      apply q.
    + apply IHn.
Qed.

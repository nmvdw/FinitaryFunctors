Require Import UniMath.Foundations.PartD.
Require Import UniMath.Foundations.Propositions.
Require Import UniMath.Foundations.Sets.
Require Import UniMath.Foundations.UnivalenceAxiom.
Require Import UniMath.Foundations.NaturalNumbers.
Require Import UniMath.Foundations.HLevels.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Local Open Scope cat.

(** ** Category HDSET of families of hSets *)
Section HDSET_precategory.

Definition hDSet : UU := ∑ (X : hSet), X → hSet.

Definition hDSet_set (X : hDSet) : hSet := pr1 X.

Definition hDSet_fam (X : hDSet) : hDSet_set X → hSet := pr2 X.

Definition hdset_fun_space (A B : hDSet) : hSet.
Proof.
  use make_hSet.
  - exact (∑ (f : hDSet_set A → hDSet_set B),
           ∏ (a : hDSet_set A), hDSet_fam A a → hDSet_fam B (f a)).
  - use isaset_total2.
    + exact (isaset_set_fun_space _ _).
    + intro f.
      use impred_isaset.
      intro x.
      exact (isaset_set_fun_space _ _).
Defined.      

Definition hdset_map {A B : hDSet} (f : hdset_fun_space A B) : hDSet_set A → hDSet_set B
  := pr1 f.

Definition hdset_map_fam {A B : hDSet} (f : hdset_fun_space A B) 
  :  ∏ (a : hDSet_set A), hDSet_fam A a → hDSet_fam B (hdset_map f a)
  := pr2 f.

Definition hdset_precategory_ob_mor : precategory_ob_mor
  := make_precategory_ob_mor hDSet hdset_fun_space.

Definition hdset_id (A : hDSet) : hdset_fun_space A A.
Proof.
  use tpair.
  - exact (λ x, x).
  - exact (λ x y, y).
Defined.
    
Definition hdset_comp (A B C : hDSet) (f : hdset_fun_space A B) (g : hdset_fun_space B C)
  : hdset_fun_space A C.
Proof.
  use tpair.
  - exact (λ x, hdset_map g (hdset_map f x)).
  - exact (λ x y, hdset_map_fam g _ (hdset_map_fam f x y)).
Defined.
    
Definition hdset_precategory_data : precategory_data.
Proof.
  use make_precategory_data.
  - exact hdset_precategory_ob_mor.
  - exact hdset_id.
  - exact hdset_comp.
Defined.

Definition hdset_is_precategory : is_precategory hdset_precategory_data.
Proof.
  repeat split.
Qed.

Definition hdset_precategory : precategory.
Proof.
  use make_precategory.
  - exact hdset_precategory_data.
  - exact hdset_is_precategory.
Defined.

Definition hdset_category : category.
Proof.
  use make_category.
  - exact hdset_precategory.
  - intros X Y.
    use isaset_total2.
    + exact (isaset_set_fun_space _ _).
    + intro f.
      use impred_isaset.
      intro x.
      exact (isaset_set_fun_space _ _).
Defined.

Local Notation "'HDSET'" := hdset_precategory : cat.
Local Notation "'DSET'" := hdset_category : cat.

Definition hset_to_hdset (X : hSet) : hDSet := (X ,, λ _, unitset).

Definition hset_to_hdset_map
           (X Y : hSet) (f : X → Y)
  : hdset_fun_space (hset_to_hdset X) (hset_to_hdset Y)
  := (f ,, λ _ _, tt).

Definition SET_to_DSET_data : functor_data SET DSET.
Proof.
  use make_functor_data.
  - exact hset_to_hdset.
  - exact hset_to_hdset_map.
Defined.

Definition SET_to_DSET_is_functor : is_functor SET_to_DSET_data.
Proof.
  use tpair.
  - intro X.
    use total2_paths2_b.
    + apply idpath.
    + apply funextsec.
      intro x.
      apply funextsec.
      intro y.
      apply iscontrpathsinunit.
  - intros X Y Z f g.
    use total2_paths2_b.
    + apply idpath.
    + apply funextsec.
      intro x.
      apply funextsec.
      intro y.
      apply iscontrpathsinunit.
Qed.
             
Definition SET_to_DSET : SET ⟶ DSET.
Proof.
  use make_functor.
  - exact SET_to_DSET_data.
  - exact SET_to_DSET_is_functor.
Defined.

Definition tot (X : hDSet) : hSet.
Proof.
  use make_hSet.
  - exact (∑ (x : hDSet_set X), hDSet_fam X x).
  - apply isaset_total2_hSet.
Defined.

Definition tot_map
           (X Y : hDSet)
           (f : hdset_fun_space X Y)
           (x : tot X)
  : tot Y.
Proof.
  use total2_base_map.
  - exact (hDSet_set X).
  - exact (hdset_map f).
  - exact (pr1 x ,, hdset_map_fam f (pr1 x) (pr2 x)).
Defined.

Definition TOT_data : functor_data DSET SET.
Proof.
  use make_functor_data.
  - exact tot.
  - exact tot_map.
Defined.

Definition TOT_is_functor : is_functor TOT_data.
Proof.
  use tpair.
  - intro X.
    apply idpath.
  - intros X Y Z f g.
    apply idpath.
Qed.
    
Definition TOT : functor DSET SET.
Proof.
  use make_functor.
  - exact TOT_data.
  - exact TOT_is_functor.
Defined.

Definition SET_to_DSET_adj_TOT : are_adjoints SET_to_DSET TOT.
Proof.
  use make_are_adjoints.
  - use make_nat_trans.
    + exact (λ X x, (x ,, tt)).
    + intros X Y f.
      apply idpath.
  - use make_nat_trans.
    + intro X.
      use (tpair _ pr1).
      exact (λ x _, pr2 x).
    + intros X Y f.
      apply idpath.
  - use tpair.
    + intro X.
      simpl.
      use total2_paths2_b.
      * apply idpath.
      * apply funextsec.
        intro x.
        apply funextsec.
        intro y.
        apply iscontrpathsinunit.
    + intro X.
      apply idpath.
Defined.

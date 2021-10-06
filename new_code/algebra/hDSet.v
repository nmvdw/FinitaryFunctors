Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.categories.HSET.All.
Require Import UniMath.CategoryTheory.Adjunctions.Core.
Require Import UniMath.CategoryTheory.Core.NaturalTransformations.

Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.
Require Import UniMath.CategoryTheory.DisplayedCats.Equivalences.

Require Import prelude.
Require Import adjunction_constructions.
Require Import syntax.containers.
Require Import syntax.hit_signature.
Require Import syntax.W_types.
Require Import algebra.set_algebra.

Local Open Scope cat.

(** ** Category HDSET of families of hSets *)
Section HDSET_precategory.

  Definition hDSet : UU := ∑ (X : hSet), X → hSet.

  Definition hDSet_set (X : hDSet) : hSet := pr1 X.

  Definition hDSet_fam (X : hDSet) : hDSet_set X → hSet := pr2 X.

  (* Note: can be split up *)
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

  (* Note: can be improved by making p a homotopy *)
  Definition hdset_fun_eq
             {A B : hDSet}
             {f g : hdset_fun_space A B}
             (p : pr1 f = pr1 g)
             (q : ∏ (x : hDSet_set A)
                    (y : hDSet_fam A x),
                  transportf
                    (hDSet_fam B)
                    (eqtohomot p x)
                    (pr2 f x y)
                  =
                  pr2 g x y)
    : f = g.
  Proof.
    induction f as [f1 f2].
    induction g as [g1 g2].
    cbn in *.
    use total2_paths_f.
    - exact p.
    - use funextsec ; intro x.
      use funextsec ; intro y.
      induction p.
      cbn in q ; cbn.
      exact (q x y).
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

  Definition hdset_category_homsets
    : has_homsets hdset_precategory_ob_mor.
  Proof.
    intros X Y.
    use isaset_total2.
    - exact (isaset_set_fun_space _ _).
    - intro f.
      use impred_isaset.
      intro x.
      exact (isaset_set_fun_space _ _).
  Qed.  

  Definition hdset_category : category.
  Proof.
    use make_category.
    - exact hdset_precategory.
    - exact hdset_category_homsets.
  Defined.

End HDSET_precategory.

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
    use hdset_fun_eq.
    + apply idpath.
    + intro x.
      intro y.
      apply iscontrpathsinunit.
  - intros X Y Z f g.
    use hdset_fun_eq.
    + apply idpath.
    + intro x.
      intro y.
      apply idpath.
Qed.
             
Definition SET_to_DSET : SET ⟶ DSET.
Proof.
  use make_functor.
  - exact SET_to_DSET_data.
  - exact SET_to_DSET_is_functor.
Defined.

Definition tot (X : hDSet) : hSet
  := (∑ (x : hDSet_set X), hDSet_fam X x)%set.

Definition tot_map
           (X Y : hDSet)
           (f : hdset_fun_space X Y)
           (x : tot X)
  : tot Y.
Proof.  use total2_base_map.
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

Definition tot_pr1 {X : hDSet} (x : tot X) : pr1 X := pr1 x.

(*
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
 *)

Definition adj_SET_DSET_unit
  : functor_identity SET ⟹ SET_to_DSET ∙ TOT.
Proof.
  use make_nat_trans.
  - exact (λ X x, (x ,, tt)).
  - abstract
      (intros X Y f ;
       apply idpath).
Defined.

Definition adj_SET_DSET_counit
  : TOT ∙ SET_to_DSET ⟹ functor_identity DSET.
Proof.
  use make_nat_trans.
  - intro X.
    use (tpair _ pr1).
    exact (λ x _, pr2 x).
  - abstract
      (intros X Y f ;
       apply idpath).
Defined.

Definition adj_SET_DSET_data : adjunction_data SET DSET.
Proof.
  refine (SET_to_DSET ,, _).
  refine (TOT ,, _).
  use tpair.
  - exact adj_SET_DSET_unit.
  - exact adj_SET_DSET_counit.
Defined.

Definition form_adj_SET_DSET : form_adjunction' adj_SET_DSET_data.
Proof.
  split.
  - intro X.
    use hdset_fun_eq.
    + apply idpath.
    + intros x y.
      apply iscontrpathsinunit.
  - intro X.
    apply idpath.
Qed.
    
Definition adj_SET_DSET : adjunction SET DSET
  := (adj_SET_DSET_data ,, form_adj_SET_DSET).

Section LiftAdjunctionPreAlg.
  Context (F : functor SET SET).

  (*
          pb --------------------> unit
           | ⌟                       |
           |                         | f
           |                         |
           V                         V
       F (tot X) ---------------> F(pr1 X)
                  #F tot_pr1 z
   *)
  (* good to split a bit, so that it becomes nicer in goals *)
  Definition DF_ob (X : hDSet) : hDSet.
  Proof.
    use tpair.
    - exact (F (pr1 X)).
    - intro f.
      simple refine (∑ (z : _), _)%set.
      + exact (F (tot X)).
      + use make_hSet.
        * exact (#F tot_pr1 z = f).
        * abstract
            (apply isasetaprop ;
             apply (F (pr1 X))).
  Defined.

  Definition DF_map
           (X Y : hDSet)
           (f : hdset_fun_space X Y)
    : hdset_fun_space (DF_ob X) (DF_ob Y).
  Proof.
    use tpair.
    - exact (#F (pr1 f)).
    - simpl.
      intros g y.
      use tpair.
      + exact (#F (tot_map _ _ f) (pr1 y)).
      + abstract
          (simpl ;
           pose (functor_comp F (tot_map X Y f) tot_pr1) as p ;
           pose (functor_comp F tot_pr1 (pr1 f)) as q ;
           exact (!(toforallpaths _ _ _ p _)
                  @ toforallpaths _ _ _ q _
                  @ maponpaths (# F (pr1 f)) (pr2 y))).
  Defined.

  Definition DF_data : functor_data DSET DSET.
  Proof.
    use make_functor_data.
    - exact DF_ob.
    - exact DF_map.
  Defined.

  Definition DF_is_functor : is_functor DF_data.
  Proof.
    use tpair.
    - intro X.
      use hdset_fun_eq.
      + apply (functor_id F).
      + intros x y.
        use subtypePath.
        {
          intro z.
          apply (F (pr1 X)).
        }
        simpl.
        etrans.
        {
          exact (pr1_transportf
                   (eqtohomot (functor_id F (pr1 X)) x)
                   _).
        }
        simpl.
        rewrite transportf_const ; cbn.
        exact (eqtohomot (functor_id F (tot X)) (pr1 y)).
    - intros X Y Z f g.
      use hdset_fun_eq.
      + apply (functor_comp F).
      + intros x y.
        use subtypePath.
        {
          intros z.
          apply (F (pr1 Z)).
        }
        simpl.
        etrans.
        {
          exact (pr1_transportf
                   (eqtohomot (functor_comp F (pr1 f) (pr1 g)) x)
                   _).
        }
        simpl.
        rewrite transportf_const ; cbn.
        exact (eqtohomot (functor_comp F (tot_map X Y f) _) (pr1 y)).
  Qed.      
            
  Definition DF : functor DSET DSET.
  Proof.
    use make_functor.
    - exact DF_data.
    - exact DF_is_functor.
  Defined.

  Definition nL : SET_to_DSET ∙ DF ⟹ F ∙ SET_to_DSET.
  Proof.
    use make_nat_trans.
    - exact (λ X, idfun _ ,, λ _ _, tt).
    - abstract
        (intros X Y f ;
         use hdset_fun_eq ;
         [ apply idpath
         | intros x y ;
           apply iscontrpathsinunit]).
  Defined.

  Definition nR_data
    : nat_trans_data (TOT ∙ F) (DF ∙ TOT)
    := λ X x, #F tot_pr1 x ,, x ,, idpath _.

  Definition nR_is_nat_trans
    : is_nat_trans _ _ nR_data.
  Proof.
    intros X Y f.
    apply funextsec.
    intro x.
    cbn.
    use total2_paths2_f.
    - simpl.
      pose (functor_comp F (tot_map X Y f) tot_pr1) as p.
      pose (functor_comp F tot_pr1 (pr1 f)) as q.          
      exact (!(toforallpaths _ _ _ p x) @ toforallpaths _ _ _ q x).
    - cbn.
      refine (transportf_total2_const _ _ _ _ _ _ _ _ @ _).
      use subtypePath.
      {
        intro.
        apply (F (pr1 Y)).
      }
      apply idpath.
  Qed.

  Definition nR : TOT ∙ F ⟹ DF ∙ TOT.
  Proof.
    use make_nat_trans.
    - exact nR_data.
    - exact nR_is_nat_trans.
  Defined.

  (* separate the triangle equations *)
  Definition fun_alg_disp_adj_SET_DSET
    : disp_adjunction
        adj_SET_DSET
        (fun_algebra_disp_cat F)
        (fun_algebra_disp_cat DF).
  Proof.
    use fun_algebra_disp_adjunction.
    - exact nL.
    - exact nR.
    - intro X.
      use hdset_fun_eq.
      + apply idpath.
      + intros x y.
        cbn.
        use total2_paths2_b.
        * exact (!(pr2 y)).
        * apply (F (pr1 X)).
    - intro X.
      apply funextsec.
      intro x.
      simpl.
      use total2_paths2_b.
      + cbn.
        pose (eqtohomot
                 (@functor_comp
                    _ _
                    F
                    X
                    (tot (hset_to_hdset X))
                    X
                    (λ z, z ,, tt)
                    tot_pr1)
                 x)
          as p.
        cbn in p.
        refine (!_ @ p).
        exact (eqtohomot (functor_id F _) x).
      + apply iscontrpathsinunit. 
  Defined.

  Definition fun_alg_adj_SET_DSET
    : adjunction
        (total_category (fun_algebra_disp_cat F))
        (total_category (fun_algebra_disp_cat DF))
    := total_adjunction fun_alg_disp_adj_SET_DSET.
End LiftAdjunctionPreAlg.


Definition TODO (A : UU) : A.
Admitted.

Section LiftAdjunctionAlg.
  Definition container_to_functorD (C : container) : DSET ⟶ DSET
    := DF (container_to_functor C).
                                                            
  Definition hit_prealgebraD (Σ : hit_signature) : category
    := total_category (fun_algebra_disp_cat (container_to_functorD (point_constr Σ))).

  (*
    Generalize sem_endpointD and sem_endpoint
   *)
  (*
  Definition sem_endpointD
             {Σ : hit_signature}
             {X : hDSet}
             (c : hdset_fun_space (container_to_functorD (point_constr Σ) X) X)
             (i : path_index Σ)
             (x : W (point_constr Σ) (path_arg Σ i)) (* the endpoint *)
             (var_set : path_arg Σ i → hDSet_set X) (* above the P *)
             (var_fam : ∏ (v : path_arg Σ i), hDSet_fam X (var_set v))
    : hDSet_fam X (sem_endpoint (hdset_map c) var_set x).
  Proof.
    induction x as [ v | s p IHp ].
    - exact (var_fam v).
    - refine (hdset_map_fam c _ _).
      refine ((s ,, λ v, sem_endpoint (hdset_map c) var_set (p v) ,, IHp v) ,, _).
      apply idpath.
  Defined.
   *)

  Check @sem_endpoint.

  (*
    ∏ (P : container)    (* point constr *)
      (X : hSet)         (* container *)
      (Q : hSet),        (* set of variables *)
    (interpret_container P X → X)   (* constructor *)
    → (Q → X)            (* interpretation of variables *)
    → W P Q              (* endpoint *)
    → X

    ∏ (P : container)    (* point constr *)
      (X : hDSet)         (* container *)
      (Q : hSet),        (* set of variables *)
    (interpret_container P X → X)   (* constructor *)
    → (Q → X)            (* interpretation of variables *)
    → W P Q              (* endpoint *)
    → X

   *)

  (*
  Given
  hdset_fun_space Q X
  return 
  hdset_fun_space (DW Q) X
   *)
  Definition funtest
             (Q : hSet)
             (X : hDSet)
    : hDSet.
  Proof.
    simple refine (_ ,, _).
    - use make_hSet.
      + refine (Q → pr1 X).
      + apply TODO.
    - simpl.
      intro q.
      use make_hSet.
      + refine (∏ (v : Q), hDSet_fam X (q v)).
      + apply TODO.
  Defined.

  (* 

     Define dependent version of covyoneda.

     Question: only for the special case when first argument is a hSet
     (as in funtest) or more general?  

     Goal: sem_endpointD is a natural transformation, similarly to sem_endpoint.
   *)
  
  Definition sem_endpointD
             {P : container}
             {X : hDSet}
             {Q : hSet}
             (c : hdset_fun_space (container_to_functorD P X) X)
             (x : W P Q) (* the endpoint *)
             (var_set : Q → hDSet_set X) (* above the P *)
             (var_fam : ∏ (v : Q), hDSet_fam X (var_set v))
    : hDSet_fam X (sem_endpoint (hdset_map c) var_set x).
  Proof.
    induction x as [ v | s p IHp ].
    - exact (var_fam v).
    - refine (hdset_map_fam c _ _).
      refine ((s ,, λ v, sem_endpoint (hdset_map c) var_set (p v) ,, IHp v) ,, _).
      apply idpath.
  Defined.

  Definition sem_endpointD_test
             {P : container}
             {X : hDSet}
             {Q : hSet}
             (c : hdset_fun_space (container_to_functorD P X) X)
             (x : W P Q) (* the endpoint *)
             (*(var_set : path_arg Σ i → hDSet_set X) (* above the P *)
             (var_fam : ∏ (v : path_arg Σ i), hDSet_fam X (var_set v))*)
    : hdset_fun_space
        (funtest Q X) 
        X.
  Proof.
    simple refine (_ ,, _).
    - intro var_set.
      exact (sem_endpoint (hdset_map c) var_set x).
    - cbn.
      intros var_set var_fam.
      exact (sem_endpointD c x var_set var_fam).
  Defined.

  Definition algD_carrier
             {Σ : hit_signature}
             (X : hit_prealgebraD Σ)
    : hDSet
    := pr1 X.

  Definition algebraD_map
             {Σ : hit_signature}
             (X : hit_prealgebraD Σ)
    : hdset_fun_space
        (container_to_functorD (point_constr Σ) (algD_carrier X))
        (algD_carrier X)
    := pr2 X.


  Locate PathOver.
  Check @PathOver.

  (*
Definition PathOver {X:Type}
           {x x':X} (p:x=x')
           {Y : X -> Type} (y : Y x) (y' : Y x') : Type.*)
  
  Definition is_hit_algebraD
             {Σ : hit_signature}
             (X : hit_prealgebraD Σ)
    : UU
    := ∏ (i : path_index Σ)
         (var_set : path_arg Σ i → hDSet_set (algD_carrier X))
         (var_fam : ∏ (v : path_arg Σ i), hDSet_fam (algD_carrier X) (var_set v)), 
       ∑ (p : sem_endpoint (hdset_map (algebraD_map X)) var_set (path_lhs Σ i)
              =
              sem_endpoint (hdset_map (algebraD_map X)) var_set (path_rhs Σ i)), 
       @PathOver
         _ _ _
         p
         (hDSet_fam (algD_carrier X))
         (sem_endpointD (algebraD_map X) (path_lhs Σ i) var_set var_fam)
         (sem_endpointD (algebraD_map X) (path_rhs Σ i) var_set var_fam).

  Definition hit_algebraD_disp_cat
             (Σ : hit_signature)
    : disp_cat (hit_prealgebraD Σ)
    := disp_full_sub _ is_hit_algebraD.
  
  Definition hit_algebraD
             (Σ : hit_signature)
    : category
    := total_category (hit_algebraD_disp_cat Σ).

  Definition adj_hit_prealgebra_hit_prealgebraD
             (Σ : hit_signature)
    : adjunction (hit_prealgebra Σ) (hit_prealgebraD Σ)
    := fun_alg_adj_SET_DSET (container_to_functor (point_constr Σ)).

(*  
  Definition sem_endpoint_tot'
             (Σ : hit_signature)
             (X : hit_prealgebraD Σ)
             (s : shapes (point_constr Σ))
             (p : positions (point_constr Σ) s
                  →
                  alg_carrier (right_functor (adj_hit_prealgebra_hit_prealgebraD Σ) X))
    : algebra_map (right_functor (adj_hit_prealgebra_hit_prealgebraD Σ) X) (s,,p)
      =
      (hdset_map (algebraD_map X) (s,, λ x, pr1 (p x))
       ,,
       hdset_map_fam (algebraD_map X) _ ((s ,, p) ,, idpath _))
    := idpath _.
 *)
  
  Definition sem_endpoint_tot
             (Σ : hit_signature)
             (X : hit_prealgebraD Σ)
             (i : path_index Σ)
             (var : path_arg Σ i
                    →
                    alg_carrier (right_functor (adj_hit_prealgebra_hit_prealgebraD Σ) X))
             (x : W (point_constr Σ) (path_arg Σ i))
    : sem_endpoint
        (algebra_map (right_functor (adj_hit_prealgebra_hit_prealgebraD Σ) X))
        i var x
      =
      (sem_endpoint
         (hdset_map (algebraD_map X))
         i
         (λ x : path_arg Σ i, tot_pr1 (var x))
         x
         ,,
       sem_endpointD
         (algebraD_map X)
         i
         (λ x : path_arg Σ i, tot_pr1 (var x))
         (λ x : path_arg Σ i, pr2 (var x))
         x).
  Proof.
    induction x as [ v | s p IHp ].
    - apply idpath.
    - use total2_paths2_b.
      + simpl.
        apply maponpaths.
        use (maponpaths (λ x, s ,, x)).
        apply funextsec.
        intro x.
        exact (maponpaths pr1 (IHp x)).
      + simpl.
        cbn.
        apply TODO.
  Qed.
       
  Definition disp_adj_hit_algebra_hit_algebraD_lem2
             (Σ : hit_signature)
             (X : hit_prealgebraD Σ)
             (i : path_index Σ)
             (var : path_arg Σ i
                    →
                    alg_carrier (right_functor (adj_hit_prealgebra_hit_prealgebraD Σ) X))
             (x y : W (point_constr Σ) (path_arg Σ i))
             (hyp_set : sem_endpoint
                          (hdset_map (algebraD_map X))
                          i
                          (λ x : path_arg Σ i, tot_pr1 (var x))
                          x
                        =
                        sem_endpoint
                          (hdset_map (algebraD_map X))
                          i
                          (λ x : path_arg Σ i, tot_pr1 (var x))
                          y)
             (hyp_fam : @PathOver
                          _ _ _
                          hyp_set
                          (hDSet_fam (algD_carrier X))
                          (sem_endpointD (algebraD_map X) i (λ x : path_arg Σ i, tot_pr1 (var x))
                                         (λ x : path_arg Σ i, pr2 (var x)) x)
                          (sem_endpointD (algebraD_map X) i (λ x : path_arg Σ i, tot_pr1 (var x))
                                         (λ x : path_arg Σ i, pr2 (var x)) y))             
    : sem_endpoint
        (algebra_map (right_functor (adj_hit_prealgebra_hit_prealgebraD Σ) X))
        i var x
      =
      sem_endpoint
        (algebra_map (right_functor (adj_hit_prealgebra_hit_prealgebraD Σ) X))
        i var y.
  Proof.
    refine (sem_endpoint_tot Σ X i var x
                             @ _
                             @ !(sem_endpoint_tot Σ X i var y)).
    use PathOverToTotalPath.
    - exact hyp_set.
    - exact hyp_fam.
  Qed.
  
  Definition disp_adj_hit_algebra_hit_algebraD
             (Σ : hit_signature)
    : disp_adjunction
        (adj_hit_prealgebra_hit_prealgebraD Σ)
        (hit_algebra_disp_cat Σ) (hit_algebraD_disp_cat Σ).
  Proof.
    use disp_full_sub_adjunction.
    - intros X X_is_hitalg i var_set var_fam.
      refine (X_is_hitalg i var_set ,, _).
      apply TODO.
    - intros X X_is_hitalgD i var.
      pose (pr1 (X_is_hitalgD i (λ x, tot_pr1 (var x)) (λ x, pr2 (var x)))) as hyp_set.
      pose (pr2 (X_is_hitalgD i (λ x, tot_pr1 (var x)) (λ x, pr2 (var x)))) as hyp_fam.
      exact (disp_adj_hit_algebra_hit_algebraD_lem2 Σ X i var _ _ hyp_set hyp_fam).
  Defined.

          
  Definition adj_hit_algebra_hit_algebraD
             (Σ : hit_signature)
    : adjunction (hit_algebra Σ) (hit_algebraD Σ)
    := total_adjunction (disp_adj_hit_algebra_hit_algebraD Σ).






  
  (*
  Definition FSET_to_FDSET_data
    : disp_functor_data
        SET_to_DSET
        (fun_algebra_disp_cat F)
        (fun_algebra_disp_cat DF).
  Proof.
    use tpair.
    - intros X a.
      refine (a ,, λ _ _, tt).
    - intros X Y a b p q.
      cbn.
      unfold hdset_comp.
      simpl.
      use total2_paths2_b.
      + exact q.
      + apply funextsec.
        intro x.
        apply funextsec.
        intro y.
        apply iscontrpathsinunit.
  Defined.
        
  Definition FSET_to_FDSET_axioms
    : disp_functor_axioms FSET_to_FDSET_data.
  Proof.
    apply TODO.
  Qed.

  Definition FSET_to_FDSET
    : disp_functor
        SET_to_DSET
        (fun_algebra_disp_cat F)
        (fun_algebra_disp_cat DF)
    := (FSET_to_FDSET_data ,, FSET_to_FDSET_axioms).

  Definition FTOT_data
    : disp_functor_data
        TOT
        (fun_algebra_disp_cat DF)
        (fun_algebra_disp_cat F).
  Proof.
    use tpair.
    - intros X a z.
      cbn in *.
      use tpair.
      + refine (pr1 a (#F _ z)).
        exact pr1.
      + exact (pr2 a _ (z ,, idpath _)).
    - simpl.
      intros X Y xx yy f p.
      apply funextsec.
      intro z.
      use total2_paths2_b.
      + simpl.
        cbn in p.
        pose (maponpaths pr1 p) as p'.
        simpl in p'.
         (toforallpaths _ _ _ p' _).
        rewrite p'.
        unfold tot_map.
        
        unfold DF_map in p.
        cbn in p.
        unfold hdset_comp in p.
        simpl in p.
        unfold hdset_map_fam in p.
        
      
      
      
      

  Definition FTOT_axioms
    : disp_functor_axioms FTOT_data
  Proof.
    apply TODO.
  Qed.
  
  Definition FTOT
    : disp_functor
        TOT
        (fun_algebra_disp_cat DF)
        (fun_algebra_disp_cat F).

        
  
  Definition disp_adj_FSET_FDSET_data
    : disp_adjunction_data
        adj_SET_DSET
        (fun_algebra_disp_cat F)
        (fun_algebra_disp_cat DF).
  Proof.
    use tpair.
    - simpl.
      
  

  Definition disp_adj_FSET_FDSET
    : disp_adjunction
        adj_SET_DSET
        (fun_algebra_disp_cat F)
        (fun_algebra_disp_cat DF).
  Proof.

*)

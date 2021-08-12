(** Here we define signatures for HITs *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.CategoryTheory.Core.Categories.
Require Import UniMath.CategoryTheory.Core.Functors.
Require Import UniMath.CategoryTheory.DisplayedCats.Core.
Require Import UniMath.CategoryTheory.DisplayedCats.Constructions.

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

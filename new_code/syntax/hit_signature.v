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

Require Import prelude.
Require Import syntax.containers.
Require Import syntax.W_types.

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

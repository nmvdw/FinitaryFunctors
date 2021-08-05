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
Require Import prelude.
Require Import syntax.containers.

(** W-types with variables *)
(*
terms, tm 
W for the W-type
 *)
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

(** Here we define signatures for HITs *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.FiniteSets.

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

Definition identity_container
  : container
  := unitset ◅ (λ _, unitset).

Definition sum_container
           (C₁ C₂ : container)
  : container
  := (setcoprod (shapes C₁) (shapes C₂)) ◅ (coprod_rect _ (positions C₁) ((positions C₂))).

Definition prod_container
           (C₁ C₂ : container)
  : container
  := (shapes C₁ × shapes C₂) ◅ (λ z, setcoprod (positions C₁ (pr1 z)) (positions C₂ (pr2 z))).

Definition exp_container
           (A : hSet)
           (C : container)
  : container
  := (funset A (shapes C)) ◅ (λ f, ∑ (a : A), positions C (f a)).

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
  : interpret_container_map C (g ∘ f)
    =
    interpret_container_map C g ∘ interpret_container_map C f.
Proof.
  apply idpath.
Qed.

(** The interpretations of the standard containers correspond with what's expected *)
Definition interpret_const_to_const
           {A : hSet}
           {X : hSet}
  : ⟦ constant_container A ⟧ X → A
  := λ x, shape_of x.

Definition const_to_interpret_const
           {A : hSet}
           {X : hSet}
  : A → ⟦ constant_container A ⟧ X
  := λ a, @cpair (constant_container _) _ a fromempty.

Definition interpret_const_to_const_to_interpret_const
           {A : hSet}
           {X : hSet}
           (x : ⟦ constant_container A ⟧ X)
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
  : ⟦ constant_container A ⟧ X ≃ A.
Proof.
  use make_weq.
  - exact interpret_const_to_const.
  - use gradth.
    + exact const_to_interpret_const.
    + exact interpret_const_to_const_to_interpret_const.
    + exact const_to_interpret_const_to_const.
Defined.

Definition interpret_identity_to_identity
           {X : hSet}
  : ⟦ identity_container ⟧ X → X
  := λ x, position_of x tt.

Definition identity_to_interpret_identity
           {X : hSet}
  : X → ⟦ identity_container ⟧ X
  := λ x, @cpair identity_container _ tt (λ _, x).

Definition interpret_identity_to_identity_to_interpret_identity
           {X : hSet}
           (x : ⟦ identity_container ⟧ X)
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
  : ⟦ identity_container ⟧ X ≃ X.
Proof.
  use make_weq.
  - exact interpret_identity_to_identity.
  - use gradth.
    + exact identity_to_interpret_identity.
    + exact interpret_identity_to_identity_to_interpret_identity.
    + exact identity_to_interpret_identity_to_identity.
Defined.


Definition interpret_prod_to_prod
           {C₁ C₂ : container}
           {X : hSet}
  : ⟦ prod_container C₁ C₂ ⟧ X → ⟦ C₁ ⟧ X × ⟦ C₂ ⟧ X
  := λ z, cpair (pr1 (shape_of z)) (λ p, position_of z (inl p))
          ,,
          cpair (pr2 (shape_of z)) (λ p, position_of z (inr p)).

Definition prod_to_interpret_prod
           {C₁ C₂ : container}
           {X : hSet}
  : ⟦ C₁ ⟧ X × ⟦ C₂ ⟧ X → ⟦ prod_container C₁ C₂ ⟧ X
  := λ z, @cpair
            (prod_container _ _)
            _
            (shape_of (pr1 z) ,, shape_of (pr2 z))
            (coprod_rect _ (position_of (pr1 z)) (position_of (pr2 z))).

Definition interpret_prod_to_prod_to_interpret_prod
           {C₁ C₂ : container}
           {X : hSet}
           (x : ⟦ prod_container C₁ C₂ ⟧ X)
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
  : ⟦ prod_container C₁ C₂ ⟧ X ≃ ⟦ C₁ ⟧ X × ⟦ C₂ ⟧ X.  
Proof.
  use make_weq.
  - exact interpret_prod_to_prod.
  - use gradth.
    + exact prod_to_interpret_prod.
    + exact interpret_prod_to_prod_to_interpret_prod.
    + exact prod_to_interpret_prod_to_prod.
Defined.

(* interpretation of sums and exponentials *)

(** Finitary containers *)
Definition is_finitary
           (C : container)
  : hProp
  := forall_hProp (λ s, isfinite (positions C s)).

(** Examples of finitary containers *)
Definition is_finitary_constant_container
           (A : hSet)
  : is_finitary (constant_container A).
Proof.
  intro s.
  apply isfiniteempty.
Qed.

Definition is_finitary_identity_container
  : is_finitary identity_container.
Proof.
  intro s.
  apply isfiniteunit.
Qed.

Definition is_finitary_sum_container
           {C₁ C₂ : container}
           (H₁ : is_finitary C₁)
           (H₂ : is_finitary C₂)
  : is_finitary (sum_container C₁ C₂).
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
  : is_finitary (prod_container C₁ C₂).
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
  : is_finitary (exp_container A C).
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

(* W C is a functor *)

Close Scope set.

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

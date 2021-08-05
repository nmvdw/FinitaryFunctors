Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import prelude.

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

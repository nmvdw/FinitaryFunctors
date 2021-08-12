Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.
Require Import UniMath.Combinatorics.FiniteSets.
Require Import UniMath.CategoryTheory.Core.Categories.

Require Import prelude.
Require Import syntax.containers.
Require Import syntax.hit_signature.
Require Import syntax.W_types.
Require Import algebra.set_algebra.

Local Open Scope container_scope.

(**
Natural numbers modulo 2

Inductive ℕ₂ : Type :=
| 0 : ℕ₂
| S : ℕ₂ → ℕ₂
| mod : ∏ (n : ℕ₂), S(S n) = n
 *)
Definition mod2_sig_point_constr
  : container.
Proof.
  use make_container.
  - exact boolset.
  - intro b.
    destruct b.
    + exact emptyset.
    + exact unitset.
Defined.

Definition mod2_sig_path_arg
  : container.
Proof.
  use make_container.
  - exact unitset.
  - exact (λ _, unitset).
Defined.

Definition mod2_sig_lhs
  : W mod2_sig_point_constr unitset.
Proof.
  simple refine (sup _ (λ _, sup _ (λ _, var _))) ; cbn.
  - exact false.
  - exact false.
  - exact tt.
Defined.

Definition mod2_sig_rhs
  : W mod2_sig_point_constr unitset.
Proof.
  apply var.
  exact tt.
Defined.

Definition mod2_sig : hit_signature.
Proof.
  use make_hit_signature.
  - exact mod2_sig_point_constr.
  - exact mod2_sig_path_arg.
  - exact (λ _, mod2_sig_lhs).
  - exact (λ _, mod2_sig_rhs).
Defined.

Definition is_finitary_mod2_sig
  : is_finitary_hit mod2_sig.
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
  Variable (X : hit_algebra mod2_sig).

  Definition mod2_carrier
    : hSet
    := pr11 X.

  Definition mod2_Z
    : mod2_carrier
    := pr21 X (true ,, fromempty).

  Definition mod2_S
    : mod2_carrier → mod2_carrier
    := λ x, pr21 X (false ,, (λ _, x)).

  Definition mod2_path
    : ∏ (n : mod2_carrier), mod2_S (mod2_S n) = n
    := λ n, pr2 X tt (λ _ , n).
End Mod2Algebra.

Definition make_mod2_algebra
           (X : hSet)
           (Z : X)
           (S : X → X)
           (p : ∏ (n : X), S(S n) = n)
  : hit_algebra mod2_sig.
Proof.
  simple refine ((X ,, _) ,, _) ; cbn.
  - intro x.
    induction x as [x arg].
    induction x ; cbn in *.
    + exact Z.
    + exact (S (arg tt)).
  - exact (λ _ n, p (n tt)).
Defined.

Definition bool_mod2_sig
  : hit_algebra mod2_sig.
Proof.
  use make_mod2_algebra.
  - exact boolset.
  - exact false.
  - exact negb.
  - intro b ; induction b ; cbn.
    + apply idpath.
    + apply idpath.
Defined.

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

Definition nat_container
  : container
  := unitset ⊕ I.

Definition nat_sig : hit_signature.
Proof.
  use make_hit_signature.
  - exact nat_container.
  - exact (constant_container emptyset).
  - cbn ; exact fromempty.
  - cbn ; exact fromempty.
Defined.

Definition is_finitary_nat_sig
  : is_finitary_hit nat_sig.
Proof.
  split.
  - intro x.
    destruct x ; cbn -[isfinite].
    + apply isfiniteempty.
    + apply isfiniteunit.
  - intro.
    apply isfiniteempty.
Qed.

Section NatAlgebra.
  Variable (X : hit_algebra nat_sig).

  Definition nat_carrier
    : hSet
    := pr11 X.

  Definition nat_Z
    : nat_carrier
    := pr21 X (inl tt ,, fromempty).

  Definition nat_S
    : nat_carrier → nat_carrier
    := λ x, pr21 X (inr tt ,, λ _, x).
End NatAlgebra.

Definition make_nat_algebra
           (X : hSet)
           (Z : X)
           (S : X → X)
  : hit_algebra nat_sig.
Proof.
  simple refine ((X ,, _) ,, λ i p, fromempty i) ; cbn.
  intro x.
  induction x as [x arg].
  induction x ; cbn in *.
  - exact Z.
  - exact (S (arg tt)).
Defined.

Definition nat_nat_sig
  : hit_algebra nat_sig.
Proof.
  use make_nat_algebra.
  - exact natset.
  - exact 0.
  - exact S.
Defined.

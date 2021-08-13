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
Groups

Inductive jsl : Type :=
| ∅ : jsl
| ∪ : jsl -> jsl -> jsl
| nl : ∏ (x : jsl), x ∪ ∅ = x
| nr : ∏ (x : jsl), ∅ ∪ x = x
| id : ∏ (x : jsl), x ∪ x = x
| assoc : ∏ (x y z : jsl), x ∪ (y ∪ z) = (x ∪ y) ∪ z
 *)
Definition jsl_operations
  : hSet
  := setcoprod unitset unitset.

Definition jsl_unit
  : jsl_operations
  := inl tt.

Definition jsl_join
  : jsl_operations
  := inr tt.

Definition jsl_arities
  : jsl_operations → hSet.
Proof.
  intro x.
  induction x as [ | ].
  - exact emptyset.
  - exact boolset.
Defined.

Definition jsl_sig_point_constr
  : container.
Proof.
  use make_container.
  - exact jsl_operations.
  - exact jsl_arities.
Defined.

Definition jsl_eqs
  : hSet
  := setcoprod
       unitset
       (setcoprod
          unitset
          (setcoprod
             unitset
             unitset)).

Definition jsl_neutral_left
  : jsl_eqs
  := inl tt.

Definition jsl_neutral_right
  : jsl_eqs
  := inr (inl tt).

Definition jsl_idem
  : jsl_eqs
  := inr (inr (inl tt)).

Definition jsl_assoc
  : jsl_eqs
  := inr (inr (inr tt)).

Definition jsl_eqs_args
  : jsl_eqs → hSet.
Proof.
  intros x.
  induction x as [ | [ | [ | ]]].
  - exact unitset.
  - exact unitset.
  - exact unitset.
  - exact (setcoprod unitset (setcoprod unitset unitset)).
Defined.

Definition jsl_sig_path_arg
  : container.
Proof.
  use make_container.
  - exact jsl_eqs.
  - exact jsl_eqs_args.
Defined.

Definition W_unit
           (A : hSet)
  : W jsl_sig_point_constr A.
Proof.
  use sup.
  - exact jsl_unit.
  - exact fromempty.
Defined.

Definition W_join
           {A : hSet}
           (x y : W jsl_sig_point_constr A)
  : W jsl_sig_point_constr A.
Proof.
  use sup.
  - exact jsl_join.
  - intro b.
    induction b.
    + exact x.
    + exact y.
Defined.

Definition jsl_sig_lhs
           (s : shapes jsl_sig_path_arg)
  : W jsl_sig_point_constr (positions jsl_sig_path_arg s).
Proof.
  induction s as [ z | [ | [ | ]]].
  - (* neutral left *)
    use W_join.
    + refine (var _).
      exact tt.
    + apply W_unit.
  - (* neutral right *)
    use W_join.
    + apply W_unit.
    + refine (var _).
      exact tt.
  - (* idempotent *)
    use W_join.
    + refine (var _).
      exact tt.
    + refine (var _).
      exact tt.
  - (* associativity *)
    use W_join.
    + refine (var _).
      exact (inl tt).
    + use W_join.
      * refine (var _).
        exact (inr (inl tt)).
      * refine (var _).
        exact (inr (inr tt)).
Defined.

Definition jsl_sig_rhs
           (s : shapes jsl_sig_path_arg)
  : W jsl_sig_point_constr (positions jsl_sig_path_arg s).
Proof.
  induction s as [ z | [ | [ | ]]].
  - (* neutral left *)
    refine (var _).
    exact tt.
  - (* neutral right *)
    refine (var _).
    exact tt.
  - (* idempotent *)
    refine (var _).
    exact tt.
  - (* associativity *)
    use W_join.
    + use W_join.
      * refine (var _).
        exact (inl tt).
      * refine (var _).
        exact (inr (inl tt)).
    + refine (var _).
      exact (inr (inr tt)).
Defined.

Definition jsl_sig : hit_signature.
Proof.
  use make_hit_signature.
  - exact jsl_sig_point_constr.
  - exact jsl_sig_path_arg.
  - exact jsl_sig_lhs.
  - exact jsl_sig_rhs.
Defined.

Definition is_finitary_jsl_sig
  : is_finitary_hit jsl_sig.
Proof.
  split.
  - intro x.
    induction x as [ | ] ; cbn -[isfinite].
    + apply isfiniteempty.
    + apply isfinitebool.
  - intro x.
    induction x as [ | [ | [ | ]]] ; cbn -[isfinite].
    + apply isfiniteunit.
    + apply isfiniteunit.
    + apply isfiniteunit.
    + use isfinitecoprod.
      * apply isfiniteunit.
      * use isfinitecoprod.
        ** apply isfiniteunit.
        ** apply isfiniteunit.
Qed.

Section JslAlgebra.
  Variable (X : hit_algebra jsl_sig).

  Definition jsl_carrier
    : hSet
    := pr11 X.

  Definition jsl_alg_unit
    : jsl_carrier
    := pr21 X (jsl_unit ,, fromempty).

  Definition jsl_alg_join
             (x y : jsl_carrier)
    : jsl_carrier.
  Proof.
    refine (pr21 X (jsl_join ,, _)).
    intro b.
    induction b.
    - exact x.
    - exact y.
  Defined.

  Local Notation "⊥" := jsl_alg_unit.
  Local Notation "x ∪ y" := (jsl_alg_join x y) (at level 30, right associativity).

  Definition jsl_alg_neutral_left
             (x : jsl_carrier)
    : x ∪ ⊥ = x.
  Proof.
    pose (p := pr2 X jsl_neutral_left (λ _, x)).
    cbn in p.
    refine (_ @ p) ; clear p.
    unfold jsl_alg_join ; cbn.
    do 2 apply maponpaths.
    use funextsec.
    intro b.
    induction b.
    - apply idpath.
    - unfold jsl_alg_unit ; cbn.
      do 2 apply maponpaths.
      use funextsec.
      intro q ; induction q.
  Qed.

  Definition jsl_alg_neutral_right
             (x : jsl_carrier)
    : ⊥ ∪ x = x.
  Proof.
    pose (p := pr2 X jsl_neutral_right (λ _, x)).
    cbn in p.
    refine (_ @ p) ; clear p.
    unfold jsl_alg_join ; cbn.
    do 2 apply maponpaths.
    use funextsec.
    intro b.
    induction b.
    - unfold jsl_alg_unit ; cbn.
      do 2 apply maponpaths.
      use funextsec.
      intro q ; induction q.
    - apply idpath.
  Qed.
  
  Definition jsl_alg_idem
             (x : jsl_carrier)
    : x ∪ x = x.
  Proof.
    pose (p := pr2 X jsl_idem (λ _, x)).
    cbn in p.
    refine (_ @ p @ _) ; clear p.
    - unfold jsl_alg_join ; cbn.
      do 2 apply maponpaths.
      use funextsec.
      intro b ; induction b ; cbn.
      + apply idpath.
      + apply idpath.
    - apply idpath.
  Qed.

  Definition jsl_alg_assoc_help
             (x y z : jsl_carrier)
    : path_arg jsl_sig jsl_assoc → alg_carrier (pr1 X).
  Proof.
    intro b.
    induction b as [ | [ | ]].
    - exact x.
    - exact y.
    - exact z.
  Defined.
  
  Definition jsl_alg_assoc
             (x y z : jsl_carrier)
    : x ∪ (y ∪ z) = (x ∪ y) ∪ z.
  Proof.
    pose (p := pr2 X jsl_assoc (jsl_alg_assoc_help x y z)).
    refine (_ @ p @ _) ; clear p.
    - unfold jsl_alg_join ; cbn.
      do 2 apply maponpaths.
      use funextsec.
      intro b ; induction b ; cbn.
      + apply idpath.
      + do 2 apply maponpaths.
        use funextsec.
        intro b ; induction b ; cbn.
        * apply idpath.
        * apply idpath.
    - unfold jsl_alg_join ; cbn.
      do 2 apply maponpaths.
      use funextsec.
      intro b ; induction b ; cbn.
      + do 2 apply maponpaths.
        use funextsec.
        intro b ; induction b ; cbn.
        * apply idpath.
        * apply idpath.
      + apply idpath.
  Defined.
End JslAlgebra.

Definition make_jsl_algebra
           (J : hSet)
           (e : J)
           (m : J → J → J)
           (nl : ∏ (x : J), m x e = x)
           (nr : ∏ (x : J), m e x = x)
           (idem : ∏ (x : J), m x x = x)
           (a : ∏ (x₁ x₂ x₃ : J),
                m x₁ (m x₂ x₃)
                =
                m (m x₁ x₂) x₃)
  : hit_algebra jsl_sig.
Proof.
  simple refine ((J ,, _) ,, _) ; cbn.
  - intro x.
    induction x as [s p].
    induction s as [ | ] ; cbn in p.
    + exact e.
    + exact (m (p true) (p false)).
  - intros j p.
    induction j as [ | [ | [ | ]]] ; cbn in p ; cbn.
    + apply nl.
    + apply nr.
    + apply idem.
    + apply a.
Defined.

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
Monoids

Inductive monoid : Type :=
| 1 : monoid
| m : monoid -> monoid -> monoid
| nl : ∏ (x : monoid), m(x, 1) = x
| nr : ∏ (x : monoid), m(1, x) = x
| assoc : ∏ (x y z : monoid), m(x, m(y, z)) = m(m(x, y), z)
 *)
Definition monoid_operations
  : hSet
  := setcoprod unitset unitset.

Definition monoid_unit
  : monoid_operations
  := inl tt.

Definition monoid_mult
  : monoid_operations
  := inr tt.

Definition monoid_arities
  : monoid_operations → hSet.
Proof.
  intro x.
  induction x as [ | ].
  - exact emptyset.
  - exact boolset.
Defined.

Definition monoid_sig_point_constr
  : container.
Proof.
  use make_container.
  - exact monoid_operations.
  - exact monoid_arities.
Defined.

Definition monoid_eqs
  : hSet
  := setcoprod
       unitset
       (setcoprod
          unitset
          unitset).

Definition monoid_neutral_left
  : monoid_eqs
  := inl tt.

Definition monoid_neutral_right
  : monoid_eqs
  := inr (inl tt).

Definition monoid_assoc
  : monoid_eqs
  := inr (inr tt).

Definition monoid_eqs_args
  : monoid_eqs → hSet.
Proof.
  intros x.
  induction x as [ | [ | ]].
  - exact unitset.
  - exact unitset.
  - exact (setcoprod unitset (setcoprod unitset unitset)).
Defined.

Definition monoid_sig_path_arg
  : container.
Proof.
  use make_container.
  - exact monoid_eqs.
  - exact monoid_eqs_args.
Defined.

Definition W_unit
           (A : hSet)
  : W monoid_sig_point_constr A.
Proof.
  use sup.
  - exact monoid_unit.
  - exact fromempty.
Defined.

Definition W_mult
           {A : hSet}
           (x y : W monoid_sig_point_constr A)
  : W monoid_sig_point_constr A.
Proof.
  use sup.
  - exact monoid_mult.
  - intro b.
    induction b.
    + exact x.
    + exact y.
Defined.

Definition monoid_sig_lhs
           (s : shapes monoid_sig_path_arg)
  : W monoid_sig_point_constr (positions monoid_sig_path_arg s).
Proof.
  induction s as [ | [ | ]].
  - (* neutral left *)
    use W_mult.
    + refine (var _).
      exact tt.
    + apply W_unit.
  - (* neutral right *)
    use W_mult.
    + apply W_unit.
    + refine (var _).
      exact tt.
  - (* associativity *)
    use W_mult.
    + refine (var _).
      exact (inl tt).
    + use W_mult.
      * refine (var _).
        exact (inr (inl tt)).
      * refine (var _).
        exact (inr (inr tt)).
Defined.

Definition monoid_sig_rhs
           (s : shapes monoid_sig_path_arg)
  : W monoid_sig_point_constr (positions monoid_sig_path_arg s).
Proof.
  induction s as [ | [ | ]].
  - (* neutral left *)
    refine (var _).
    exact tt.
  - (* neutral right *)
    refine (var _).
    exact tt.
  - (* associativity *)
    use W_mult.
    + use W_mult.
      * refine (var _).
        exact (inl tt).
      * refine (var _).
        exact (inr (inl tt)).
    + refine (var _).
      exact (inr (inr tt)).
Defined.

Definition monoid_sig : hit_signature.
Proof.
  use make_hit_signature.
  - exact monoid_sig_point_constr.
  - exact monoid_sig_path_arg.
  - exact monoid_sig_lhs.
  - exact monoid_sig_rhs.
Defined.

Definition is_finitary_monoid_sig
  : is_finitary_hit monoid_sig.
Proof.
  split.
  - intro x.
    induction x as [ | ] ; cbn -[isfinite].
    + apply isfiniteempty.
    + apply isfinitebool.
  - intro x.
    induction x as [ | [ | ]] ; cbn -[isfinite].
    + apply isfiniteunit.
    + apply isfiniteunit.
    + use isfinitecoprod.
      * apply isfiniteunit.
      * use isfinitecoprod.
        ** apply isfiniteunit.
        ** apply isfiniteunit.
Qed.

Section MonoidAlgebra.
  Variable (X : hit_algebra monoid_sig).

  Definition monoid_carrier
    : hSet
    := pr11 X.

  Definition monoid_alg_unit
    : monoid_carrier
    := pr21 X (monoid_unit ,, fromempty).

  Definition monoid_alg_mult
             (x y : monoid_carrier)
    : monoid_carrier.
  Proof.
    refine (pr21 X (monoid_mult ,, _)).
    intro b.
    induction b.
    - exact x.
    - exact y.
  Defined.

  Local Notation e := monoid_alg_unit.
  Local Notation "x · y" := (monoid_alg_mult x y).

  Definition monoid_alg_neutral_left
             (x : monoid_carrier)
    : x · e = x.
  Proof.
    pose (p := pr2 X monoid_neutral_left (λ _, x)).
    cbn in p.
    refine (_ @ p) ; clear p.
    unfold monoid_alg_mult ; cbn.
    do 2 apply maponpaths.
    use funextsec.
    intro b.
    induction b.
    - apply idpath.
    - unfold monoid_alg_unit ; cbn.
      do 2 apply maponpaths.
      use funextsec.
      intro q ; induction q.
  Qed.

  Definition monoid_alg_neutral_right
             (x : monoid_carrier)
    : e · x = x.
  Proof.
    pose (p := pr2 X monoid_neutral_right (λ _, x)).
    cbn in p.
    refine (_ @ p) ; clear p.
    unfold monoid_alg_mult ; cbn.
    do 2 apply maponpaths.
    use funextsec.
    intro b.
    induction b.
    - unfold monoid_alg_unit ; cbn.
      do 2 apply maponpaths.
      use funextsec.
      intro q ; induction q.
    - apply idpath.
  Qed.
  
  Definition monoid_alg_assoc_help
             (x y z : monoid_carrier)
    : path_arg monoid_sig monoid_assoc → alg_carrier (pr1 X).
  Proof.
    intro b.
    induction b as [ | [ | ]].
    - exact x.
    - exact y.
    - exact z.
  Defined.
  
  Definition monoid_alg_assoc
             (x y z : monoid_carrier)
    : x · (y · z) = (x · y) · z.
  Proof.
    pose (p := pr2 X monoid_assoc (monoid_alg_assoc_help x y z)).
    refine (_ @ p @ _) ; clear p.
    - unfold monoid_alg_mult ; cbn.
      do 2 apply maponpaths.
      use funextsec.
      intro b ; induction b ; cbn.
      + apply idpath.
      + do 2 apply maponpaths.
        use funextsec.
        intro b ; induction b ; cbn.
        * apply idpath.
        * apply idpath.
    - unfold monoid_alg_mult ; cbn.
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
End MonoidAlgebra.

Definition make_monoid_algebra
           (G : hSet)
           (e : G)
           (i : G → G)
           (m : G → G → G)
           (nl : ∏ (g : G), m g e = g)
           (nr : ∏ (g : G), m e g = g)
           (a : ∏ (g₁ g₂ g₃ : G),
                m g₁ (m g₂ g₃)
                =
                m (m g₁ g₂) g₃)
  : hit_algebra monoid_sig.
Proof.
  simple refine ((G ,, _) ,, _) ; cbn.
  - intro x.
    induction x as [s p].
    induction s as [ | ] ; cbn in p.
    + exact e.
    + exact (m (p true) (p false)).
  - intros j p.
    induction j as [ | [ | ]] ; cbn in p ; cbn.
    + apply nl.
    + apply nr.
    + apply a.
Defined.

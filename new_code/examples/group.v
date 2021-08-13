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

Inductive group : Type :=
| 1 : group
| i : group -> group
| m : group -> group -> group
| nl : ∏ (x : group), m(x, 1) = x
| nr : ∏ (x : group), m(1, x) = x
| il : ∏ (x : group), m(x, i x) = 1
| ir : ∏ (x : group), m(i x, x) = 1
| assoc : ∏ (x y z : group), m(x, m(y, z)) = m(m(x, y), z)
 *)
Definition group_operations
  : hSet
  := setcoprod unitset (setcoprod unitset unitset).

Definition group_unit
  : group_operations
  := inl tt.

Definition group_inv
  : group_operations
  := inr (inl tt).

Definition group_mult
  : group_operations
  := inr (inr tt).

Definition group_arities
  : group_operations → hSet.
Proof.
  intro x.
  induction x as [ | [ | ]].
  - exact emptyset.
  - exact unitset.
  - exact boolset.
Defined.

Definition group_sig_point_constr
  : container.
Proof.
  use make_container.
  - exact group_operations.
  - exact group_arities.
Defined.

Definition group_eqs
  : hSet
  := setcoprod
       unitset
       (setcoprod
          unitset
          (setcoprod
             unitset
             (setcoprod
                unitset
                unitset))).

Definition group_neutral_left
  : group_eqs
  := inl tt.

Definition group_neutral_right
  : group_eqs
  := inr (inl tt).

Definition group_inv_left
  : group_eqs
  := inr (inr (inl tt)).

Definition group_inv_right
  : group_eqs
  := inr (inr (inr (inl tt))).

Definition group_assoc
  : group_eqs
  := inr (inr (inr (inr tt))).

Definition group_eqs_args
  : group_eqs → hSet.
Proof.
  intros x.
  induction x as [ | [ | [ | [ | ]]]].
  - exact unitset.
  - exact unitset.
  - exact unitset.
  - exact unitset.
  - exact (setcoprod unitset (setcoprod unitset unitset)).
Defined.

Definition group_sig_path_arg
  : container.
Proof.
  use make_container.
  - exact group_eqs.
  - exact group_eqs_args.
Defined.

Definition W_unit
           (A : hSet)
  : W group_sig_point_constr A.
Proof.
  use sup.
  - exact group_unit.
  - exact fromempty.
Defined.

Definition W_inv
           {A : hSet}
           (x : W group_sig_point_constr A)
  : W group_sig_point_constr A.
Proof.
  use sup.
  - exact group_inv.
  - exact (λ _, x).
Defined.

Definition W_mult
           {A : hSet}
           (x y : W group_sig_point_constr A)
  : W group_sig_point_constr A.
Proof.
  use sup.
  - exact group_mult.
  - intro b.
    induction b.
    + exact x.
    + exact y.
Defined.

Definition group_sig_lhs
           (s : shapes group_sig_path_arg)
  : W group_sig_point_constr (positions group_sig_path_arg s).
Proof.
  induction s as [ z | [ | [ | [ | ]]]].
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
  - (* inverse left *)
    use W_mult.
    + refine (var _).
      exact tt.
    + apply W_inv.
      refine (var _).
      exact tt.
  - (* inverse right *)
    use W_mult.
    + apply W_inv.
      refine (var _).
      exact tt.
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

Definition group_sig_rhs
           (s : shapes group_sig_path_arg)
  : W group_sig_point_constr (positions group_sig_path_arg s).
Proof.
  induction s as [ | [ | [ | [ | ]]]].
  - (* neutral left *)
    refine (var _).
    exact tt.
  - (* neutral right *)
    refine (var _).
    exact tt.
  - (* inverse left *)
    apply W_unit.
  - (* inverse right *)
    apply W_unit.
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

Definition group_sig : hit_signature.
Proof.
  use make_hit_signature.
  - exact group_sig_point_constr.
  - exact group_sig_path_arg.
  - exact group_sig_lhs.
  - exact group_sig_rhs.
Defined.

Definition is_finitary_group_sig
  : is_finitary_hit group_sig.
Proof.
  split.
  - intro x.
    induction x as [ | [ | ]] ; cbn -[isfinite].
    + apply isfiniteempty.
    + apply isfiniteunit.
    + apply isfinitebool.
  - intro x.
    induction x as [ | [ | [ | [ | ]]]] ; cbn -[isfinite].
    + apply isfiniteunit.
    + apply isfiniteunit.
    + apply isfiniteunit.
    + apply isfiniteunit.
    + use isfinitecoprod.
      * apply isfiniteunit.
      * use isfinitecoprod.
        ** apply isfiniteunit.
        ** apply isfiniteunit.
Qed.

Section GroupAlgebra.
  Variable (X : hit_algebra group_sig).

  Definition group_carrier
    : hSet
    := pr11 X.

  Definition group_alg_unit
    : group_carrier
    := pr21 X (group_unit ,, fromempty).

  Definition group_alg_inv
             (x : group_carrier)
    : group_carrier
    := pr21 X (group_inv ,, λ _, x).

  Definition group_alg_mult
             (x y : group_carrier)
    : group_carrier.
  Proof.
    refine (pr21 X (group_mult ,, _)).
    intro b.
    induction b.
    - exact x.
    - exact y.
  Defined.

  Local Notation e := group_alg_unit.
  Local Notation "x · y" := (group_alg_mult x y).
  Local Notation "! x" := (group_alg_inv x).

  Definition group_alg_neutral_left
             (x : group_carrier)
    : x · e = x.
  Proof.
    pose (p := pr2 X group_neutral_left (λ _, x)).
    cbn in p.
    refine (_ @ p) ; clear p.
    unfold group_alg_mult ; cbn.
    do 2 apply maponpaths.
    use funextsec.
    intro b.
    induction b.
    - apply idpath.
    - unfold group_alg_unit ; cbn.
      do 2 apply maponpaths.
      use funextsec.
      intro q ; induction q.
  Qed.

  Definition group_alg_neutral_right
             (x : group_carrier)
    : e · x = x.
  Proof.
    pose (p := pr2 X group_neutral_right (λ _, x)).
    cbn in p.
    refine (_ @ p) ; clear p.
    unfold group_alg_mult ; cbn.
    do 2 apply maponpaths.
    use funextsec.
    intro b.
    induction b.
    - unfold group_alg_unit ; cbn.
      do 2 apply maponpaths.
      use funextsec.
      intro q ; induction q.
    - apply idpath.
  Qed.
  
  Definition group_alg_inverse_left
             (x : group_carrier)
    : x · (!x) = e.
  Proof.
    pose (p := pr2 X group_inv_left (λ _, x)).
    cbn in p.
    refine (_ @ p @ _) ; clear p.
    - unfold group_alg_mult, group_alg_inv ; cbn.
      do 2 apply maponpaths.
      use funextsec.
      intro b ; induction b ; cbn.
      + apply idpath.
      + apply idpath.
    - unfold group_alg_unit.
      do 2 apply maponpaths.
      use funextsec.
      intro b ; induction b.
  Qed.

  Definition group_alg_inverse_right
             (x : group_carrier)
    : (!x) · x = e.
  Proof.
    pose (p := pr2 X group_inv_right (λ _, x)).
    cbn in p.
    refine (_ @ p @ _) ; clear p.
    - unfold group_alg_mult, group_alg_inv ; cbn.
      do 2 apply maponpaths.
      use funextsec.
      intro b ; induction b ; cbn.
      + apply idpath.
      + apply idpath.
    - unfold group_alg_unit.
      do 2 apply maponpaths.
      use funextsec.
      intro b ; induction b.
  Qed.

  Definition group_alg_assoc_help
             (x y z : group_carrier)
    : path_arg group_sig group_assoc → alg_carrier (pr1 X).
  Proof.
    intro b.
    induction b as [ | [ | ]].
    - exact x.
    - exact y.
    - exact z.
  Defined.
  
  Definition group_alg_assoc
             (x y z : group_carrier)
    : x · (y · z) = (x · y) · z.
  Proof.
    pose (p := pr2 X group_assoc (group_alg_assoc_help x y z)).
    refine (_ @ p @ _) ; clear p.
    - unfold group_alg_mult ; cbn.
      do 2 apply maponpaths.
      use funextsec.
      intro b ; induction b ; cbn.
      + apply idpath.
      + do 2 apply maponpaths.
        use funextsec.
        intro b ; induction b ; cbn.
        * apply idpath.
        * apply idpath.
    - unfold group_alg_mult ; cbn.
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
End GroupAlgebra.

Definition make_group_algebra
           (G : hSet)
           (e : G)
           (i : G → G)
           (m : G → G → G)
           (nl : ∏ (g : G), m g e = g)
           (nr : ∏ (g : G), m e g = g)
           (il : ∏ (g : G), m g (i g) = e)
           (ir : ∏ (g : G), m (i g) g = e)
           (a : ∏ (g₁ g₂ g₃ : G),
                m g₁ (m g₂ g₃)
                =
                m (m g₁ g₂) g₃)
  : hit_algebra group_sig.
Proof.
  simple refine ((G ,, _) ,, _) ; cbn.
  - intro x.
    induction x as [s p].
    induction s as [ | [ | ]] ; cbn in p.
    + exact e.
    + exact (i (p tt)).
    + exact (m (p true) (p false)).
  - intros j p.
    induction j as [ | [ | [ | [ | ]]]] ; cbn in p ; cbn.
    + apply nl.
    + apply nr.
    + apply il.
    + apply ir.
    + apply a.
Defined.

Require Import Basics.
Require Import Types.
Require Import Fibrations.
Require Import AbelianGroup.
Require Import Algebra.Group.
Require Import Algebra.Subgroup.
Require Import WildCat.

(** Kernels of abelian groups *)

Local Open Scope mc_add_scope.

Definition grp_kernel {A B : AbGroup} (f : GroupHomomorphism A B) : AbGroup.
Proof.
  serapply (Build_AbGroup (hfiber f abgroup_unit)); repeat split.
  + (** Operation *)
    intros [a p] [b q].
    exists (a + b).
    rewrite grp_homo_op, p, q.
    apply left_identity.
  + (** Unit *)
    exists mon_unit.
    apply (grp_homo_unit f).
  + (** Inverse *)
    intros [a p].
    exists (-a).
    rewrite grp_homo_inv, p.
    exact negate_mon_unit.
  + (** HSet *)
    exact _.
  + intros [a p] [b q] [c r].
    serapply path_sigma_hprop.
    cbn; apply associativity.
  + intros [a p].
    serapply path_sigma_hprop.
    cbn; apply left_identity.
  + intros [a p].
    serapply path_sigma_hprop.
    cbn; apply right_identity.
  + intros [a p].
    serapply path_sigma_hprop.
    cbn; apply left_inverse.
  + intros [a p].
    serapply path_sigma_hprop.
    cbn; apply right_inverse.
  + intros [a p] [b q].
    serapply path_sigma_hprop.
    cbn; apply commutativity.
Defined.

Definition grp_homo_kernel_pr1 {A B : AbGroup} (f : GroupHomomorphism A B)
  : GroupHomomorphism (grp_kernel f) A.
Proof.
  serapply Build_GroupHomomorphism.
  - apply pr1.
  - intros a b; reflexivity.
Defined.

Global Instance isinjective_grp_homo_kernel_pr1 {A B : AbGroup}
  (f : GroupHomomorphism A B) : IsInjective (grp_homo_kernel_pr1 f).
Proof.
  intros a b.
  apply path_sigma_hprop.
Defined.

Global Instance issubgroup_grp_kernel {A B : AbGroup}
  (f : GroupHomomorphism A B) : IsSubgroup (grp_kernel f) A.
Proof.
  serapply Build_IsSubgroup.
  + exact (grp_homo_kernel_pr1 f).
  + intros a b.
    apply path_sigma_hprop.
Defined.

Definition AbKernel {A B : AbGroup} (f : GroupHomomorphism A B)
  : Subgroup A := Build_Subgroup A (grp_kernel f) _.

Global Instance isnormal_abkernel {A B : AbGroup} (f : GroupHomomorphism A B)
  : IsNormalSubgroup (AbKernel f) := _.


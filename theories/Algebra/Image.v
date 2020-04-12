Require Import Basics Types.
Require Import HFiber.
Require Import Algebra.AbelianGroup.
Require Import Algebra.Group.
Require Import Algebra.Subgroup.
Require Import WildCat.
Require Import Truncations.
Require Import Factorization.

Local Open Scope mc_add_scope.

(** The image of a group homomorphisms between abelian groups is an abelian group *)
Definition grp_image {A B : AbGroup} (f : A $-> B) : AbGroup.
Proof.
  (** The underlying type is the (propositional) image of the type *)
  srapply (Build_AbGroup (image (Tr (-1)) f)); repeat split.
  + (** Group operation *)
    intros [a p] [b q].
    exists (a + b).
    strip_truncations.
    apply tr.
    exists (p.1 + q.1).
    rewrite grp_homo_op.
    rewrite p.2, q.2. 
    reflexivity.
  + (** Group unit *)
    exists mon_unit.
    apply tr.
    exists mon_unit.
    apply (grp_homo_unit f).
  + (** Group inverse *)
    intros [a p].
    exists (- a).
    strip_truncations.
    apply tr.
    exists (- p.1).
    rewrite grp_homo_inv.
    apply ap, p.2.
  + exact _.
  + intros [a p] [b q] [c r].
    srapply path_sigma_hprop.
    cbn; apply associativity.  
  + intros [a p].
    srapply path_sigma_hprop.
    cbn; apply left_identity.
  + intros [a p].
    srapply path_sigma_hprop.
    cbn; apply right_identity.
  + intros [a p].
    srapply path_sigma_hprop.
    cbn; apply left_inverse.
  + intros [a p].
    srapply path_sigma_hprop.
    cbn; apply right_inverse.
  + intros [a p] [b q].
    srapply path_sigma_hprop.
    cbn; apply commutativity.
Defined.

Definition grp_image_pr1 {A B : AbGroup} (f : A $-> B)
  : grp_image f $-> B.
Proof.
  srapply Build_GroupHomomorphism.
  + apply pr1.
  + intros ??; reflexivity.
Defined.

Definition grp_image_in {A B : AbGroup} (f : A $-> B)
  : A $-> grp_image f.
Proof.
  srapply Build_GroupHomomorphism.
  + intro a.
    exists (f a).
    apply tr.
    exists a.
    reflexivity.
  + intros x y.
    apply path_sigma_hprop.
    apply (grp_homo_op f).
Defined.

Global Instance isinjective_grp_image_pr1 {A B : AbGroup} (f : A $-> B)
  : IsInjective (grp_image_pr1 f).
Proof.
  intros a b.
  apply path_sigma_hprop.
Defined.

Global Instance issubgroup_grp_image {A B : AbGroup}
  (f : A $-> B) : IsSubgroup (grp_image f) B
  := Build_IsSubgroup _ _ (grp_image_pr1 f) _.

Definition AbImage {A B : AbGroup} (f : A $-> B)
  : Subgroup B := Build_Subgroup _ (grp_image f) _.



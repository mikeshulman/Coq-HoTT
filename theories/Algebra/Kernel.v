Require Import Basics Types.
Require Import Algebra.Groups.
Require Import Algebra.AbGroups.AbelianGroup.
Require Import WildCat.

(** Kernels of abelian groups *)

Local Open Scope mc_add_scope.

Definition abgrp_kernel {A B : AbGroup} (f : GroupHomomorphism A B) : AbGroup
  := Build_AbGroup' (grp_kernel f).

Global Instance isnormal_abkernel {A B : AbGroup} (f : GroupHomomorphism A B)
  : IsNormalSubgroup (abgrp_kernel f) := _.


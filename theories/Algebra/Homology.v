Require Import Basics Types.
Require Import Groups AbGroups.
Require Import GradedAbGroup.
Require Import WildCat.

Definition ab_homology {A B C : AbGroup} (f : A $-> B) (g : B $-> C) : AbGroup.
Proof.
  snrapply QuotientAbGroup.
  1: exact (abgrp_kernel g).
  apply subgroup_intersection_pr2.
  1: exact (grp_image f).
Defined.

Definition Homology {G M M' M''}
  (psi : @GradedHomomorphism G M' M'')
  (phi : GradedHomomorphism M M')
  : GradedGroup G
  := fun x =>
    Build_AbGroup' (ab_homology (gh_component_prev phi x) (gh_component psi x)).



Require Import Algebra.Group.
Require Import Algebra.AbelianGroup.
Require Import Algebra.GradedAbGroup.
Require Import Algebra.QuotientGroup.
Require Import Algebra.Kernel.
Require Import Algebra.Image.
Require Import Algebra.Subgroup.
Require Import WildCat.

Definition ab_homology {A B C : AbGroup} (f : A $-> B) (g : B $-> C)
  : AbGroup
  := Build_AbGroup (QuotientGroup (AbKernel g)
      (subgroup_intersection_pr2 (AbImage f) (AbKernel g))) _ _ _ _.

Definition Homology {G M M' M''}
  (psi : @GradedHomomorphism G M' M'')
  (phi : GradedHomomorphism M M')
  : GradedGroup G
  := fun x =>
    Build_AbGroup (ab_homology (gh_component_prev phi x) (gh_component psi x))
      _ _ _ _.



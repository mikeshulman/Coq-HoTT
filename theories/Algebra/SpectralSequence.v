Require Import Basics.
Require Import Types.
Require Import Algebra.Group.
Require Import Algebra.AbelianGroup.
Require Import Algebra.GradedAbGroup.
Require Import Algebra.Homology.

(** Spectral sequences *)

Record SpectralSequence (G : AbGroup) := {
  E (r : nat) : GradedGroup G;
  d (r : nat) : GradedHomomorphism (E r) (E r);
  d_is_differential : forall r, gh_compose (d r) (d r) = gh_zero;
  alpha (r : nat) (g : G)
    : GroupIsomorphism
      (Homology (d r) (d r) g)
      (E r.+1 g);
}.

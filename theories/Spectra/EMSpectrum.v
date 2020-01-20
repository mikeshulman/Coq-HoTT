Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Homotopy.EMSpace.
Require Import AbelianGroup.
Require Import Spectrum.

Definition EMSpectrum `{Univalence} (A : AbGroup) : Spectrum.
Proof.
  serapply Build_Spectrum_nat.
  1: exact (EilenbergMacLane A).
  intro n. symmetry. apply pequiv_loops_em_em.
Defined.
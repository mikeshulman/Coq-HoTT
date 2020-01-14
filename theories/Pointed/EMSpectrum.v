Require Import Basics.
Require Import Types.
Require Import Pointed.
Require Import Homotopy.EMSpace.
Require Import AbelianGroup.
Require Import Spectrum.

(** TODO: unfinished *)
Definition EMSpectrum `{Univalence} (A : AbGroup) : Spectrum.
Proof.
  serapply Build_Spectrum.
  1: exact (EilenbergMacLane A).
  { intro n.
    apply pointed_equiv_fun.
    symmetry.
    exact pequiv_loops_em_em. }
  intro n.
  exact _.
Defined.
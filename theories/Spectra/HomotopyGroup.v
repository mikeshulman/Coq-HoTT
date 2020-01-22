Require Import HoTT.Basics.
Require Import Pointed.
(* Require Import HoTT.Truncations. *)
Require Import SuccessorStructure.
Require Import WildCat.
Require Import Homotopy.HomotopyGroup Homotopy.Splice.
Require Import Spaces.Int.
Require Import Spectra.Spectrum Spectra.GeneralizedSpectrum.
Require Import Algebra.AbelianGroup Algebra.Group.

Local Open Scope int_scope.


(** Homotopy groups of spectra *)

Definition sPi (n : Int) (Y : Spectrum) : AbGroup 
  := Build_AbGroup' (H := isabgroup_pi _ _) (Pi 2 (Y (2 - n))).

Definition spi_functor (n : Int) {E F : Spectrum} (f : E $-> F) 
  : sPi n E $-> sPi n F 
  := pi_functor 2 (f (2 - n)).

Definition spi_isomorphism_of_pequiv (n : Int) {E F : Spectrum} (f : forall n, E n $<~> F n) :
    sPi n E $<~> sPi n F :=
  groupiso_pi_functor 1 (f (2 - n)).

Definition sPi_isomorphism_of_pequiv_nat (n : nat) {E F : Spectrum}
    (f : forall n : nat, E (n) $<~> F n) : sPi n E $<~> sPi n F.
Admitted.
(*   sPi_isomorphism_of_pequiv n (Spectrum_pequiv_of_nat f). *)

Definition equiv_glue_neg (X : Spectrum) (n : Int) : X (2 - int_succ n) $<~> loops (X (2 - n)).
Proof.
  refine  (_ $oE _). 2: exact (equiv_glue X (2 - int_succ n)).
  apply pequiv_loops_functor. apply pequiv_path. apply ap.
  refine (ap int_succ (int_sub_add _ _ _) @ int_sub_add_cancel _ _).
Defined.

Definition pi_glue (X : Spectrum) (n : Int) : 
  (Pi 2 (X (2 - int_succ n)) : Group) $<~> Pi 3 (X (2 - n)) 
  := groupiso_pi_functor 1 (equiv_glue_neg X n).

Definition pi_glue_natural {X Y : Spectrum} (f : X $-> Y) (n : Int) :
    Square (pi_glue X n) (pi_glue Y n)
           (pi_functor 2 (f (2 - int_succ n))) (pi_functor 3 (f (2 - n))).
Proof.
(*     change pi_functor 2 (equiv_glue_neg Y n) o* pi_functor 2 (f (2 - succ n)) ==*
           pi_functor 2 (Ω-> (f (2 - n))) o* pi_functor 2 (equiv_glue_neg X n),
    refine pi_functor_psquare 2 _ =>
    refine !sglue_square @v* ap1_psquare !pequiv_of_eq_natural^-1*
 *)
Admitted.

(*
Definition forall g_glue_homotopy_pi_glue (X : Spectrum) (n : Int) : forall g_glue X n == pi_glue X n :=
  by reflexivity

Definition pi_glue_natural {X Y : Spectrum} (f : X $-> Y) (n : Int) :
    pi_glue Y n o* pi_functor 2 (f (2 - succ n)) ==* pi_functor 3 (f (2 - n)) o* pi_glue X n :=
Proof.
    change pi_functor 2 (equiv_glue_neg Y n) o* pi_functor 2 (f (2 - succ n)) ==*
           pi_functor 2 (Ω-> (f (2 - n))) o* pi_functor 2 (equiv_glue_neg X n),
    refine pi_functor_psquare 2 _ =>
    refine !sglue_square @v* ap1_psquare !pequiv_of_eq_natural^-1*
Defined.
*)
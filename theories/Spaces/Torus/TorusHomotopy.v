Require Import Basics.
Require Import Types.
Require Import Algebra.Group.
Require Import Algebra.AbelianGroup.
Require Import Homotopy.Pi1S1.
Require Import Algebra.Z.
Require Import Pointed.
Require Import Spaces.Int.
Require Import HIT.Circle.
Require Import Truncations.
Require Import Homotopy.HomotopyGroup.

Require Import Torus.
Require Import TorusEquivCircles.

Local Open Scope trunc_scope.
Local Open Scope pointed_scope.

(** The torus is 1-truncated *)

Global Instance is1type_Torus `{Univalence} : IsTrunc 1 Torus.
Proof.
  refine (trunc_equiv _ equiv_torus_prod_S1^-1).
Qed.

(** The torus is 0-connected *)

Global Instance isconnected_Torus `{Univalence} : IsConnected 0 Torus.
Proof.
  srapply (isconnected_equiv' _ _ equiv_torus_prod_S1^-1).
  srapply (isconnected_equiv' _ _ (equiv_sigma_prod0 _ _)).
Qed.

(** We give these notations for the pointed versions. *)
Local Notation T := (Build_pType Torus _).
Local Notation S1 := (Build_pType S1 _).

(** Loop space of Torus *)
Theorem loops_torus `{Univalence} : loops T <~>* Int * Int.
Proof.
  srefine (_ o*E _).
  1: exact (loops (S1 * S1)).
  1: apply pequiv_loops_functor.
  { srapply Build_pEquiv.
    1: srapply Build_pMap.
    1: exact equiv_torus_prod_S1.
    1: reflexivity.
    exact _. }
  srefine (_ o*E _).
  1: exact (loops S1 * loops S1).
  1: apply loops_prod.
  snrapply Build_pEquiv.
  1: srapply Build_pMap.
  { apply functor_prod.
    1,2: apply equiv_loopS1_int. }
  1: reflexivity.
  exact _.
Defined.

Lemma pequiv_torus_prod_circles `{Funext} : T  <~>* S1 * S1.
Proof.
  srapply Build_pEquiv'.
  1: apply equiv_torus_prod_S1.
  reflexivity.
Defined.

(* Fundamental group of Torus *)

Theorem Pi1Torus `{Univalence}
  : GroupIsomorphism (Pi 1 T) (group_prod Z Z).
Proof.
  etransitivity.
  { apply groupiso_pi_functor.
    apply pequiv_torus_prod_circles. }
  etransitivity.
  1: apply pi_prod.
  apply grp_iso_prod.
  1,2: apply Pi1Circle.
Defined.

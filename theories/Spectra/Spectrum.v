(* -*- mode: coq; mode: visual-line -*- *)

(** * Spectra *)

Require Import HoTT.Basics.
Require Import HoTT.Types.
(* Require Import HoTT.Tactics. *)
Require Import Pointed.

(* Require Import HoTT.Truncations. *)
Require Import SuccessorStructure.
Require Import GeneralizedSpectrum.
Require Import Spaces.Int Spaces.Pos.

(* Require Import . *)

(* Import TrM. *)

(* Local Open Scope nat_scope. *)
(* Local Open Scope path_scope. *)
(* Local Open Scope equiv_scope. *)
Local Open Scope pointed_scope.
Local Open Scope succ_scope.

(** Definition of Z-spectra *)

Definition Prespectrum := GenPrespectrum IntSucc.
Definition Spectrum := GenSpectrum IntSucc.

Definition Build_Spectrum' (X : Int -> pType)
  (f : forall n : Int, X n ->* loops (X (int_succ n)))
  {H : forall n : Int, IsEquiv (f n)}
  : Spectrum
  := Build_GenSpectrum' IntSucc
      (Build_GenPrespectrum IntSucc X f) H.

Definition Build_Spectrum (X : Int -> pType)
  (f : forall n : Int, X n <~>* loops (X (int_succ n)))
  : Spectrum
  := Build_GenSpectrum IntSucc X f.


(** END: move to pos *)

Definition Build_Spectrum_nat (X : nat -> pType)
  (f : forall n, X n <~>* loops (X (S n)))
  : Spectrum.
Proof.
  srapply Build_Spectrum.
  + intros [n| |p].
    - exact (iterated_loops n (X O)).
    - exact (X O).
    - exact (X p).
  + intros [n| |p].
    - revert n. refine (pos_peano_ind _ _ _). 
      * reflexivity.
      * intros n _. rewrite nat_pos_succ, int_succ_pos_succ. reflexivity.
    - simpl. exact (f O).
    - rewrite int_succ_pos, nat_pos_succ. apply f.
Defined.

(** ** Truncations of spectra *)
(*
Definition strunc `{Univalence} (k : trunc_index) (E : Spectrum) : Spectrum.
Proof.
  simple refine (Build_Spectrum (Build_Prespectrum (fun n => pTr (trunc_index_inc k n) (E n)) _) _).
  - intros n.
    exact ((ptr_loops _ (E n.+1)) o*E (ptr_pequiv _ (equiv_glue E n))).
  - intros n. unfold glue.
    srapply isequiv_compose.
Defined.
*)
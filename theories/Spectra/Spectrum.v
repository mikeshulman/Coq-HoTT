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
Require Import WildCat.

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

Definition Spectrum_pequiv_of_pequiv_succ {E F : Spectrum} (n : Int) 
  (e : E (int_succ n) $<~> F (int_succ n))
  : E n $<~> F n :=
  (equiv_glue F n)^-1$ $oE pequiv_loops_functor e $oE equiv_glue E n.

Definition Spectrum_pequiv_of_nat {E F : Spectrum} 
  (e : forall (n : nat), E n $<~> F n) (n : Int) 
  : E n $<~> F n.
Proof.
    induction n as [n| |p].
    { revert n. refine (pos_peano_ind _ _ _). 
      { apply Spectrum_pequiv_of_pequiv_succ. exact (e O). }
      { intros n IH. apply Spectrum_pequiv_of_pequiv_succ.
        rewrite int_succ_pos_succ. exact IH. } }
    { exact (e O). }
    { rewrite pos_int_nat. exact (e p). }
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
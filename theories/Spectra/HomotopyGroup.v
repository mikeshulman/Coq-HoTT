Require Import HoTT.Basics.
Require Import Pointed.
(* Require Import HoTT.Truncations. *)
Require Import SuccessorStructure.
Require Import WildCat.
Require Import Homotopy.HomotopyGroup Homotopy.Splice Homotopy.ExactSequence.
Require Import Spaces.Int.
Require Import Spectra.Spectrum Spectra.GeneralizedSpectrum.
Require Import Algebra.Groups Algebra.AbGroups.

Local Open Scope int_scope.


(** Homotopy groups of spectra *)

Definition sPi (n : Int) (Y : Spectrum) : AbGroup 
  := Build_AbGroup' (Pi 2 (Y (2 - n))).

Definition spi_functor (n : Int) {E F : Spectrum} (f : E $-> F) 
  : sPi n E $-> sPi n F 
  := pi_functor 2 (f (2 - n)).

Definition spi_isomorphism_of_pequiv (n : Int) {E F : Spectrum} 
  (f : forall n, E n $<~> F n) 
  : sPi n E $<~> sPi n F :=
  groupiso_pi_functor 1 (f (2 - n)).

Definition spi_isomorphism_of_pequiv_nat (n : nat) {E F : Spectrum}
    (f : forall n : nat, E n $<~> F n) 
  : sPi n E $<~> sPi n F :=
  spi_isomorphism_of_pequiv n (Spectrum_pequiv_of_nat f).

Definition equiv_glue_neg (X : Spectrum) (n : Int) 
  : X (2 - int_succ n) $<~> loops (X (2 - n)).
Proof.
  refine  (_ $oE _). 2: exact (equiv_glue X (2 - int_succ n)).
  apply pequiv_loops_functor. apply pequiv_path. apply ap.
  refine (ap int_succ (int_sub_add _ _ _) @ int_sub_add_cancel _ _).
Defined.

Definition pi_glue (X : Spectrum) (n : Int) 
  : (Pi 2 (X (2 - int_succ n)) : Group) $<~> Pi 3 (X (2 - n)) 
  := groupiso_pi_functor 1 (equiv_glue_neg X n).

(* This is reflexivity, but we give a proof to speed up the compilation. *)
Definition pi_functor_3 {X Y : pType} (f : X $-> Y)
  : pi_functor 3 f $== pi_functor 2 (loops_functor f).
Proof.
  refine (pi_functor_succ f 2 $@ _ $@ (pi_functor_succ (loops_functor f) 1)^$).
  reflexivity.
Defined.

Definition pequiv_path_natural {A : Type} {B C : A -> pType} 
  (f : forall a, B a $-> C a)
  {a1 a2 : A} (p : a1 = a2) 
  : Square (A:=pType) (pequiv_path (ap B p)) (pequiv_path (ap C p)) (f a1) (f a2).
Proof.
  induction p. exact (vrefl _).
Defined.

Definition pi_glue_natural {X Y : Spectrum} (f : X $-> Y) (n : Int) :
    Square (A := Group) 
           (pi_glue X n) (pi_glue Y n)
           (pi_functor 2 (f (2 - int_succ n))) (pi_functor 3 (f (2 - n))).
Proof.
  refine (_ $@vR _).
  2: apply pi_functor_3.
  refine (fmap_square (Pi 2) _).
  refine (smap_square _ _ _ _ $@v _). 
  refine (fmap_square loops _).
  apply pequiv_path_natural.
Defined.

Local Open Scope nat_scope.
Local Open Scope succ_scope.
(** The long exact sequence of homotopy groups for spectra *)

Local Notation "'f0'" := (inl (inl (inr tt))).
Local Notation "'f1'" := (inl (inr tt)).
Local Notation "'f2'" := (inr tt).

Definition Pi_les_fn_eq_0 `{Univalence} {F X Y : pType} (i : F $-> X) (f : X $-> Y) 
  `{IsExact oo _ _ _ i f} (n : nat) : les_fn (Pi_les i f) (S n, f0) $== pi_functor (S n) f.
Proof.
  symmetry. apply pmap_pi_functor.
Defined.

Definition Pi_les_fn_eq_1 `{Univalence} {F X Y : pType} (i : F $-> X) (f : X $-> Y) 
  `{IsExact oo _ _ _ i f} (n : nat) : les_fn (Pi_les i f) (S n, f1) $== pi_functor (S n) i.
Proof.
  symmetry. apply pmap_pi_functor.
Defined.

Definition sPi_les `{Univalence} {F X Y : Spectrum} (i : F $-> X) (f : X $-> Y) 
  `{forall n, IsExact oo (i n) (f n)} : LongExactSequence (Tr (-1)) (Z3).
Proof.
  srapply (splice (fun n : +Z => Pi_les (i (2 - n)) (f (2 - n))) (2, f0) _ _ _).
  all: cbn beta.
  { intro n. exact (pequiv_groupisomorphism (pi_glue Y n)). }
  { intro n. exact (pequiv_groupisomorphism (pi_glue X n)). }
  { intro n. pose (fmap_square ptype_group (pi_glue_natural f n)). 
    (* Unfortunately, not all of these maps are definitionally equal to the above map. *)
    refine (_ $@vL _ $@vR _).
    1,3: apply Pi_les_fn_eq_0.
    exact s. }
Defined.

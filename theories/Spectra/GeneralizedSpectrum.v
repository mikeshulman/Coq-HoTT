(* -*- mode: coq; mode: visual-line -*- *)

(** * Spectra *)

Require Import HoTT.Basics HoTT.Types.
Require Import HoTT.Tactics.
Require Import Pointed.
(* Require Import HoTT.Truncations. *)
Require Import SuccessorStructure.
Require Import WildCat.

(* Import TrM. *)

(* Local Open Scope nat_scope. *)
(* Local Open Scope path_scope. *)
(* Local Open Scope equiv_scope. *)
Local Open Scope pointed_scope.

(** ** Basic Definitions of Spectra *)

Local Open Scope succ_scope.

Record GenPrespectrum (N : SuccStr) := {
  deloop :> N -> pType ;
  glue : forall n, deloop n ->* loops (deloop (n .+1))
}.

Arguments deloop {_}.
Arguments glue {_}.

Class IsSpectrum {N : SuccStr} (E : GenPrespectrum N) :=
  is_equiv_glue : forall n, IsEquiv (glue E n).

Existing Instance is_equiv_glue.

Definition equiv_glue {N : SuccStr} (E : GenPrespectrum N)
  `{!IsSpectrum E}
  : forall n, E n <~>* loops (E n.+1)
  := fun n => Build_pEquiv _ _ (glue E n) _.

Record GenSpectrum (N : SuccStr) := Build_GenSpectrum'
{
   to_gen_prespectrum :> GenPrespectrum N;
   to_gen_is_spectrum : IsSpectrum to_gen_prespectrum;
}.

Existing Instance to_gen_is_spectrum.

Definition Build_GenSpectrum (N : SuccStr) (X : N -> pType) (f : forall n, X n <~>* loops (X n.+1)) 
  : GenSpectrum N
:= Build_GenSpectrum' N
    (Build_GenPrespectrum N X f) (fun _ => _).

Section GenSpectrum.

  Context {N : SuccStr}.



  Record sMap (X Y : GenPrespectrum N) := {
    spectrum_fun :> forall n, X n ->* Y n;
    smap_square : forall n, Square (spectrum_fun n) (loops_functor (spectrum_fun n.+1)) (glue X n) (glue Y n); }.

  Arguments smap_square {_ _}.

  Definition smap_idmap (X : GenPrespectrum N) : sMap X X.
  Proof.
    serapply Build_sMap.
    + intro; exact pmap_idmap.
    + intro. exact (hrfl $@vR loops_functor_idmap _).
  Defined.

  Definition smap_compose {X Y Z : GenPrespectrum N}
    : sMap Y Z -> sMap X Y -> sMap X Z.
  Proof.
    intros f g.
    serapply Build_sMap.
    + refine (fun n => f n o* g n).
    + intro n. simpl. 
      exact ((smap_square g n $@h smap_square f n) $@vR loops_functor_compose _ _).
  Defined.

  Global Instance is01cat_genprespectrum : Is01Cat (GenPrespectrum N).
  Proof.
    serapply Build_Is01Cat.
    + exact sMap.
    + exact smap_idmap.
    + cbn; intros X Y Z.
      exact smap_compose.
  Defined.

  Global Instance is1cat_genprespectrum : Is1Cat (GenPrespectrum N).
  Proof.
    serapply Build_Is1Cat.
    + intros X Y.
      serapply Build_Is01Cat.
      - (* homotopies between spectra maps *)
        admit.
      - admit.
      - admit.
    + admit.
  Admitted.

Global Instance is01cat_genspectrum : Is01Cat (GenSpectrum N) :=
  induced_01cat (to_gen_prespectrum _).

Definition sConst (X Y : GenPrespectrum N) : X $-> Y.
Proof.
  refine (Build_sMap X Y (fun n => pConst) _).
  intro n. refine (precompose_pconst _ @* (postcompose_pconst _)^* @* pmap_prewhisker _ (loops_functor_pconst)^*).
Defined.

(** Fiber of a spectrum map. *)
Definition sfiber {X Y : GenSpectrum N} (f : X $-> Y) : GenSpectrum N.
Proof.
  apply (Build_GenSpectrum N (fun n => pfiber (f n))).
  intro n. exact (pfiber_loops_functor _ o*E pequiv_pfiber (equiv_glue X n) (equiv_glue Y n) (smap_square f n)).
Defined.

Definition sfib {X Y : GenSpectrum N} (f : X $-> Y) : sfiber f $-> X.
Proof.
  serapply Build_sMap; intro n.
  + exact (pfib (f n)).
  + refine (move_left_bottom _). refine (_ $@vR _).
  1: apply square_functor_pfiber.
  apply pr1_pfiber_loops_functor.
Defined.

(** Sections of parametrized spectra *)

Definition spi (A : pType) (Y : A -> GenSpectrum N) : GenSpectrum N.
Proof.
  apply (Build_GenSpectrum N (fun n => ).
  intro n. exact (pfiber_loops_functor _ o*E pequiv_pfiber (equiv_glue X n) (equiv_glue Y n) (smap_square f n)).
Defined.

  definition spi [constructor] {N : succ_str} (A : Type*) (E : A → gen_spectrum N) :
    gen_spectrum N :=
  spectrum.MK (λn, Π*a, E a n)
    (λn, !loop_pppi_pequiv⁻¹ᵉ* ∘*ᵉ ppi_pequiv_right (λa, equiv_glue (E a) n))

  definition spi_compose_left [constructor] {N : succ_str} {A : Type*} {E F : A -> gen_spectrum N}
    (f : Πa, E a →ₛ F a) : spi A E →ₛ spi A F :=
  smap.mk (λn, pppi_compose_left (λa, f a n))
    begin
      intro n,
      exact psquare_pppi_compose_left (λa, (glue_square (f a) n)) ⬝v*
        (ptranspose !loop_pppi_pequiv_natural_right)⁻¹ᵛ*
    end

End GenSpectrum.



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
    smap_htpy : forall n,
      (glue Y n) o* (spectrum_fun n)
      ==* (loops_functor (spectrum_fun n.+1)) o* (glue X n);
  }.

  Arguments smap_htpy {_ _}.

  Definition smap_idmap (X : GenPrespectrum N) : sMap X X.
  Proof.
    serapply Build_sMap.
    + intro; exact pmap_idmap.
    + intro.
      cbn.
      refine (cat_idr _ $@ _).
      refine ((cat_idl _)^$ $@ _).
      refine (_ $@R _).
      symmetry.
      apply loops_functor_idmap.
  Defined.

  Definition smap_compose {X Y Z : GenPrespectrum N}
    : sMap Y Z -> sMap X Y -> sMap X Z.
  Proof.
    intros f g.
    serapply Build_sMap.
    + refine (fun n => f n o* g n).
    + intro n.
      simpl.
      refine ((cat_assoc _ _ _)^$ $@ _).
      refine (smap_htpy f _ $@R _ $@ _).
      symmetry.
      refine (loops_functor_compose _ _ $@R _ $@ _).
      refine (_ $@ (cat_assoc _ _ _)^$).
      refine (cat_assoc _ _ _ $@ _).
      refine (_ $@L (smap_htpy g _)^$).
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
    intro n. refine (pfiber_loops_functor _ o*E _).
  Admitted.
(*  definition sfiber [constructor] {N : succ_str} {X Y : gen_spectrum N} (f : X →ₛ Y) :
    gen_spectrum N :=
    spectrum.MK (λn, pfiber (f n))
       (λn, (loop_pfiber (f (S n)))⁻¹ᵉ* ∘*ᵉ pfiber_pequiv_of_square _ _ (sglue_square f n))

  /- the map from the fiber to the domain -/
  definition spoint {N : succ_str} {X Y : gen_spectrum N} (f : X →ₛ Y) : sfiber f →ₛ X :=
  smap.mk (λn, ppoint (f n))
    begin
      intro n,
--      refine _ ⬝vp* !ppoint_loop_pfiber_inv,
      refine _ ⬝* !passoc,
      refine _ ⬝* pwhisker_right _ !ppoint_loop_pfiber_inv⁻¹*,
      rexact (pfiber_pequiv_of_square_ppoint (equiv_glue X n) (equiv_glue Y n) (sglue_square f n))⁻¹*
    end*)


End GenSpectrum.



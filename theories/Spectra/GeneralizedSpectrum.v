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

Record GenSpectrum (N : SuccStr) := 
{
   to_gen_prespectrum :> GenPrespectrum N;
   to_gen_is_spectrum : IsSpectrum to_gen_prespectrum;
}.

Existing Instance to_gen_is_spectrum.

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

  Global Instance is01cat_genspectrum : Is01Cat (GenSpectrum N).
  Proof.
    serapply Build_Is01Cat.
    + exact sMap.
    + exact smap_idmap.
    + cbn; intros X Y Z.
      exact smap_compose.
  Defined.

  Global Instance is1cat_genspectrum : Is1Cat (GenSpectrum N).
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

End GenSpectrum.



(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.Overture.
Require Import Basics.PathGroupoids.
Require Import Basics.Notations.
Require Import Basics.Contractible.
Require Import Basics.Equivalences.
Require Import WildCat.Core.
Require Import WildCat.FunctorCat.

(** ** Wild category of wild categories *)

Record WildCat :=Pl
{
  cat_carrier : Type;
  cat_is0coh1cat : Is0Coh1Cat cat_carrier;
  
  (* TODO: How much should we include here? Plan: do for objects 0 coherent 1 categories; then consider 1 coherent 1 categories.*)
}.

Coercion cat_carrier : WildCat >-> Sortclass. (* note for morgan: this allows us to consider WildCats as types. *)

Global Existing Instance cat_is0coh1cat.

Global Instance is0coh1cat_wildcat : Is0Coh1Cat WildCat.
Proof.
  serapply Build_Is0Coh1Cat.
  + intros A B.  
  exact (Fun1 A B).
  + intros C. cbn in *.
  unfold Fun1. 
  (** This part seems redundant. I'm showing idmap is a 0 coherent 1 functor. maybe done elsewhere? (or should be done somewhere else?). In modifying we will probably want that idmap is 0 coherent 2, 1 coherent 1, etc. *)
  exists (idmap). serapply Build_Is0Coh1Functor. intros a b. cbn.
  exact (idmap).
  + intros A B C; cbn in *; unfold Fun1.
  intros [G g] [F f]. 
  exists ( G o F). 
  serapply Build_Is0Coh1Functor.
  intros u v h. cbn in *.  exact (fmap G ( fmap F h)).
  Defined.

Global Instance is0coh2cat_wildcat : Is0Coh2Cat WildCat.
Proof.
Admitted.
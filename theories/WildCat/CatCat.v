(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.Overture.
Require Import Basics.PathGroupoids.
Require Import Basics.Notations.
Require Import Basics.Contractible.
Require Import Basics.Equivalences.
Require Import WildCat.Core.
Require Import WildCat.FunctorCat.
Require Import WildCat.Equiv.

(** ** Wild category of wild categories *)

Record WildCat01 :=Pl
{
  cat01_carrier : Type;
  cat01_is01cat : Is01Cat cat01_carrier;
  
  (* TODO: How much should we include here? Plan: do for objects 0 coherent 1 categories; then consider 1 coherent 1 categories.*)
}.

Coercion cat01_carrier : WildCat01 >-> Sortclass. (* note for morgan: this allows us to consider WildCats as types. *)

Global Existing Instance cat01_is01cat.

Global Instance is01cat_wildcat01 : Is01Cat WildCat01.
Proof.
  serapply Build_Is01Cat.
  + intros A B.  
    exact (Fun01 A B).
  + intros C. cbn in *.
    exists (idmap). 
    exact _.
  + intros A B C [G g] [F f].
    exists (G o F). 
    serapply Build_Is0Functor.
    intros u v h. cbn in *.
    exact (fmap G ( fmap F h)).
Defined.

  (** Next: require more coherences to be a WildCat; get that WildCat is itself more structured. *) 

Record WildCat :=
{
  cat_carrier : Type;
  cat_is01cat : Is01Cat cat_carrier;
  cat_is1cat : Is1Cat cat_carrier
}.

Coercion cat_carrier : WildCat >-> Sortclass. 

(* note for morgan: this allows us to consider WildCats as types. *)
Global Existing Instance cat_is01cat. 
Global Existing Instance cat_is1cat.

(** The proof below is identical to that showing that WildCat01 is a 0 coherent 1 category. This is because every 1 coherent 1 category is a 0 coherent 1 category. *)
Global Instance is01cat_wildcat : Is01Cat WildCat.
Proof.
  serapply Build_Is01Cat.
  + intros A B.
  exact (Fun01 A B).
  + intro C.
  exists idmap. exact _.
  + intros C D E; cbn in *. 
  intros [F f]. intros [G g].
  exists (F o G). 
  serapply Build_Is0Functor.
  intros a b h. cbn in *. exact (fmap F( fmap G h)).
Defined.


(** Need to have a way to take the core of Fun1 A B to get a gropoid so that we can have a 2-category structure on WildCat.*)

Definition core (A : Type) `{Is01Cat A} := A.

Global Instance is01cat_core (A : Type) `{HasEquivs A}
  : Is01Cat (core A).
Proof.
  serapply Build_Is01Cat.
  + intros a b. 
Admitted.

Global Instance is0gpd_core (A : Type) `{HasEquivs A}
  : Is0Gpd (core A).
Proof.
  rapply Build_Is0Gpd.
Admitted.

(* Now show WildCat is a 2-category with a 1-category structure on Fun02 given by natural transformations. *) 

Global Instance is1cat_wildcat : Is1Cat WildCat.
(** Proof.
  serapply Build_Is1Coh1Cat.
  + intros A B C D f g h.
  exact (Fun1 A B).
  + intros C. cbn in *.
  unfold Fun1. 
  exists (idmap). serapply Build_Is0Coh1Functor. intros a b. cbn.
  exact (idmap).
  + intros A B C; cbn in *; unfold Fun1.
  intros [G g] [F f]. 
  exists ( G o F). 
  serapply Build_Is0Coh1Functor.
  intros u v h. cbn in *.  exact (fmap G ( fmap F h)).
  Defined. *)
Admitted. 



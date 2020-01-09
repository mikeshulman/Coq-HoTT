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
  cat01_is0coh1cat : Is0Coh1Cat cat01_carrier;
  
  (* TODO: How much should we include here? Plan: do for objects 0 coherent 1 categories; then consider 1 coherent 1 categories.*)
}.

Coercion cat01_carrier : WildCat01 >-> Sortclass. (* note for morgan: this allows us to consider WildCats as types. *)

Global Existing Instance cat01_is0coh1cat.

Global Instance is0coh1cat_wildcat01 : Is0Coh1Cat WildCat01.
Proof.
  serapply Build_Is0Coh1Cat.
  + intros A B.  
  exact (Fun01 A B).
  + intros C. cbn in *.
  exists (idmap). 
  exact _.
  + intros A B C; cbn in *; unfold Fun01.
  intros [G g] [F f]. 
  exists ( G o F). 
  serapply Build_Is0Coh1Functor.
  intros u v h. cbn in *.  exact (fmap G ( fmap F h)).
  Defined.
  
  (** Next: require more coherences to be a WildCat; get that WildCat is itself more structured. *) 

Record WildCat :=P2
{
  cat_carrier : Type; cat_is0coh1cat : Is0Coh1Cat cat_carrier;
   cat_is0coh2cat : Is0Coh21Cat cat_carrier; 
   cat_is1coh1cat : Is1Coh1Cat cat_carrier}.

Coercion cat_carrier : WildCat >-> Sortclass. 

(* note for morgan: this allows us to consider WildCats as types. *)
Global Existing Instance cat_is1coh1cat. 
Global Existing Instance cat_is0coh2cat.
Global Existing Instance cat_is0coh1cat.

(** The proof below is identical to that showing that WildCat01 is a 0 coherent 1 category. This is because every 1 coherent 1 category is a 0 coherent 1 category. *)
Global Instance is0coh1cat_wildcat : Is0Coh1Cat WildCat.
Proof.
  serapply Build_Is0Coh1Cat.
  + intros A B.
  exact (Fun01 A B).
  + intro C. unfold Fun01. 
  exists idmap. exact _.
  + intros C D E; cbn in *. 
  intros [F f]. intros [G g].
  unfold Fun01.
  exists (F o G). 
  serapply Build_Is0Coh1Functor.
  intros a b h. cbn in *. exact (fmap F( fmap G h)).
  Defined.


(** Need to have a way to take the core of Fun1 A B to get a gropoid so that we can have a 0 coherent 2 category structure on WildCat.*)

Definition core (A : Type) `{h : Is0Coh1Cat A} := A.

Global Instance is0coh1cat_core (A : Type) `{ h : Is0Coh1Cat(A)} : Is0Coh1Cat ( core A).
Proof. serapply Build_Is0Coh1Cat.
  + intros a b. 
  
Admitted.

Global Instance is0coh1gpd_core (A : Type) `{ h : Is0Coh1Cat(A)} : Is0Coh1Gpd ( core A).
Proof. rapply Build_Is0Coh1Gpd.
Admitted.

(* now show WildCat is 0 coh 2 cat with 0 coh 1 category structure on Fun02 given by taking core f natural transoformations. *) 

Global Instance is0coh21cat_wildcat : Is0Coh21Cat WildCat.
Proof.
Admitted.

Global Instance is1coh1cat_wildcat : Is1Coh1Cat WildCat.
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
  Defined. *) Admitted. 



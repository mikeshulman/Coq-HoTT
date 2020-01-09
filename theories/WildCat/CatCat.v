(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.Overture.
Require Import Basics.PathGroupoids.
Require Import Basics.Notations.
Require Import Basics.Contractible.
Require Import Basics.Equivalences.
Require Import WildCat.Core.

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
(*
  refine (Build_Is0Coh1Cat WildCat (fun A B => Fun1 A B) _ _). *)
Admitted.

Global Instance is0coh2cat_wildcat : Is0Coh2Cat WildCat.
Proof.
Admitted.
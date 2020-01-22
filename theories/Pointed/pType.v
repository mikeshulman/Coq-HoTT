(* -*- mode: coq; mode: visual-line -*- *)
Require Import Basics Types UnivalenceImpliesFunext.
Require Import Pointed.Core.
Require Import WildCat.
Require Import pHomotopy pMap pEquiv.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

Global Instance is0functor_pointed_type : Is0Functor pointed_type.
Proof.
  apply Build_Is0Functor. intros. exact f.
Defined.
  
Global Instance is1functor_pointed_type : Is1Functor pointed_type.
Proof.
  apply Build_Is1Functor.
  + intros ? ? ? ? h. exact h.
  + intros. reflexivity.
  + intros. reflexivity.
Defined.

(* TODO: generalize to wild categories with 0 object. *)
Definition hconst_square {A B C D : pType} {f : A $-> B} {g : C $-> D} : 
  Square pConst pConst f g :=
  precompose_pconst g $@ (postcompose_pconst f)^$.

Definition vconst_square {A B C D : pType} {f : A $-> B} {g : C $-> D} : 
  Square f g pConst pConst :=
  postcompose_pconst f $@ (precompose_pconst g)^$.

(* -*- mode: coq; mode: visual-line -*- *)
Require Import Basics.
Require Import Pointed.Core.
Require Import WildCat.
Require Import pHomotopy.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

Global Instance is0coh1cat_ptype : Is0Coh1Cat pType
  := Build_Is0Coh1Cat pType pMap (@pmap_idmap) (@pmap_compose).
  
  (** pointed homotopy stuff. *)
  
  Global Instance is0coh1cat_pmap (A B : pType) : Is0Coh1Cat (A ->* B).
Proof.
  srapply (Build_Is0Coh1Cat (A ->* B) (@pHomotopy A B)).
  - reflexivity.
  - intros a b c f g; transitivity b; assumption.
Defined.

Global Instance is0coh1gpd_pmap (A B : pType) : Is0Coh1Gpd (A ->* B).
Proof.
  srapply Build_Is0Coh1Gpd.
  intros; symmetry; assumption.
Defined.

Global Instance is0coh2cat_ptype : Is0Coh21Cat pType.
Proof.
  rapply Build_Is0Coh21Cat; try exact _.
  intros A B C; rapply Build_Is0Coh1Functor; intros [f1 f2] [g1 g2] [p q]; cbn.
  transitivity (f1 o* g2).
  - apply pmap_postwhisker; assumption.
  - apply pmap_prewhisker; assumption.
Defined. 





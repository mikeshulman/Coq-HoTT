Require Import Basics.
Require Import WildCat.Core.

(** Unit category *)

Global Instance isgraph_unit : IsGraph Unit.
Proof.
  serapply Build_IsGraph.
  intros ? ?; exact Unit.
Defined.

Global Instance is0coh1cat_unit : Is0Coh1Cat Unit.
Proof.
  by serapply Build_Is0Coh1Cat'.
Defined.

Global Instance is0coh1gpd_unit :    Is0Coh1Gpd Unit.
Proof.
  by serapply Build_Is0Coh1Gpd.
Defined.

Global Instance is0coh21cat_unit : Is0Coh21Cat Unit.
Proof.
  serapply Build_Is0Coh21Cat; try exact _.
  intros ? ? ?.
  by serapply Build_Is0Coh1Functor.
Defined.

Global Instance is1coh1cat_unit : Is1Coh1Cat Unit.
Proof.
  by serapply Build_Is1Coh1Cat.
Defined.


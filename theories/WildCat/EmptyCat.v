Require Import Basics.
Require Import WildCat.Core.

(** Empty category *)

Global Instance isgraph_empty : IsGraph Empty.
Proof.
  by econstructor.
Defined.

Global Instance is0coh1cat_empty : Is0Coh1Cat Empty.
Proof.
  by econstructor.
Defined.

Global Instance is0coh1gpd_empty : Is0Coh1Gpd Empty.
Proof.
  by econstructor.
Defined.

Global Instance is0coh21cat_empty : Is0Coh21Cat Empty.
Proof.
  by simple notypeclasses refine (Build_Is0Coh21Cat _ _ _ _ _).
Defined.

Global Instance is1coh1cat_empty : Is1Coh1Cat Empty.
Proof.
  econstructor; intros [].
Defined.


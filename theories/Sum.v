(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Import WildCat.Core.

(** ** Sum categories *)

Global Instance is0coh1cat_sum A B `{ Is0Coh1Cat A } `{ Is0Coh1Cat B}
  : Is0Coh1Cat (A + B).
Proof.
  serapply Build_Is0Coh1Cat.
  - intros [a1 | b1] [a2 | b2].
    + exact (a1 $-> a2).
    + exact Empty.
    + exact Empty.
    + exact (b1 $-> b2).
  - intros [a | b]; apply Id.
  - intros [a | b] [a1 | b1] [a2 | b2];
    try contradiction; apply cat_comp.
Defined.

(* Note: [try contradiction] deals with empty cases. *)
Global Instance is0coh2cat_sum A B `{ Is0Coh2Cat A } `{ Is0Coh2Cat B}
  : Is0Coh2Cat (A + B).
Proof.
  serapply Build_Is0Coh2Cat.
  - intros x y.
    serapply Build_Is0Coh1Cat;
    destruct x as [a1 | b1], y as [a2 | b2];
    try contradiction; cbn;
    (apply Hom || apply Id || intros a b c; apply cat_comp).
  - intros x y; serapply Build_Is0Coh1Gpd.
    destruct x as [a1 | b1], y as [a2 | b2];
    try contradiction; cbn; intros f g; apply gpd_rev.
  - intros x y z; serapply Build_Is0Coh1Functor.
    intros [f g] [h i] [j k].
    destruct x as [a1 | b1], y as [a2 | b2], z as [a3 | b3];
    try contradiction; exact (j $o@ k).
Defined.

Global Instance is1coh1cat_sum A B `{Is1Coh1Cat A} `{Is1Coh1Cat B}
  : Is1Coh1Cat (A + B).
Proof.
  serapply Build_Is1Coh1Cat.
  { intros [a1 | b1] [a2 | b2] [a3 | b3] [a4 | b4] f g h;
    try contradiction; cbn; apply cat_assoc. }
  1,2: intros [a1 | b1] [a2 | b2] f; try contradiction;
    cbn; ( apply cat_idl || apply cat_idr).
Defined.

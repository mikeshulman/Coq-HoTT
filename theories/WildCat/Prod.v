(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.Overture.
Require Import Basics.PathGroupoids.
Require Import Basics.Notations.
Require Import Basics.Contractible.
Require Import Basics.Equivalences.
Require Import WildCat.Core.
Require Import WildCat.Equiv.


(** ** Product categories *)

(** This is already in core.
Global Instance is0coh1cat_prod A B `{Is0Coh1Cat A} `{Is0Coh1Cat B}
  : Is0Coh1Cat (A * B).
Proof.
  refine (Build_Is0Coh1Cat (A * B) (fun x y => (fst x $-> fst y) * (snd x $-> snd y)) _ _).
  - intros [a b]; exact (Id a, Id b).
  - intros [a1 b1] [a2 b2] [a3 b3] [f1 g1] [f2 g2]; cbn in *.
    exact (f1 $o f2 , g1 $o g2).
Defined.

Global Instance is0coh1gpd_prod A B `{Is0Coh1Gpd A} `{Is0Coh1Gpd B} : Is0Coh1Gpd (A * B).
Proof. 
    serapply Build_Is0Coh1Gpd.
    intros [x1 x2] [y1 y2] [f1 f2].
    cbn in *.
    exact ( (f1^$, f2^$) ).
Defined.

Global Instance is0coh21cat_prod A B `{Is0Coh21Cat A} `{Is0Coh21Cat B}
  : Is0Coh21Cat (A * B).
Proof.
  serapply (Build_Is0Coh21Cat).
  - intros [x1 x2] [y1 y2].
    rapply is0coh1cat_prod.
  - intros [x1 x2] [y1 y2].
    apply is0coh1gpd_prod.
    + cbn.
      apply isgpd_hom.
    + cbn.
      apply isgpd_hom.
  - intros [x1 x2] [y1 y2] [z1 z2].
    serapply Build_Is0Coh1Functor.  
    intros f g. unfold uncurry. destruct f as [[f11 f12] [f21 f22]]. destruct g as [[g11 g12] [g21 g22]]. cbn in *. 
    intros a. destruct a as [[a11 a12][a21 a22]].
    exact ( a11 $o@ a21, a12 $o@ a22).
Defined.
    
Global Instance is1coh1cat_prod A B `{Is1Coh1Cat A} `{Is1Coh1Cat B}
  : Is1Coh1Cat (A * B).
Proof.
  srefine (Build_Is1Coh1Cat (A * B) _ _ _ ).
  - intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] [f1 f2] [g1 g2] [h1 h2].
    cbn in *. 
    exact(cat_assoc f1 g1 h1, cat_assoc f2 g2 h2).
  - intros [a1 a2] [b1 b2] [f1 f2].
    cbn in *.
    exact (cat_idl _, cat_idl _).
  - intros [a1 a2] [b1 b2] [g1 g2].
    cbn in *.
    exact (cat_idr _, cat_idr _). 
Defined. 
*)

Global Instance hasequivs_prod A B `{HasEquivs A} `{HasEquivs B}
  : HasEquivs (A * B).
Proof.
  srefine (Build_HasEquivs (A * B) _ _
             (fun a b => (fst a $<~> fst b) * (snd a $<~> snd b))
             _ _ _ _ _ _ _ _ _).
  1:intros a b f; exact (CatIsEquiv (fst f) * CatIsEquiv (snd f)).
  all:cbn; intros a b f.
  - split; [ exact (fst f) | exact (snd f) ].
  - split; exact _.
  - intros [fe1 fe2]; split.
    + exact (Build_CatEquiv (fst f)).
    + exact (Build_CatEquiv (snd f)).
  - intros [fe1 fe2]; cbn; split; apply cate_buildequiv_fun.
  - intros [fe1 fe2]; split; [ exact ((fst f)^-1$) | exact ((snd f)^-1$) ].
  - intros [fe1 fe2]; split; apply cate_issect.
  - intros [fe1 fe2]; split; apply cate_isretr.
  - intros g r s; split.
    + exact (catie_adjointify (fst f) (fst g) (fst r) (fst s)).
    + exact (catie_adjointify (snd f) (snd g) (snd r) (snd s)).
Defined.

Global Instance isequivs_prod A B `{HasEquivs A} `{HasEquivs B}
       {a1 a2 : A} {b1 b2 : B} {f : a1 $-> a2} {g : b1 $-> b2}
       {ef : CatIsEquiv f} {eg : CatIsEquiv g}
  : @CatIsEquiv (A*B) _ _ _ (a1,b1) (a2,b2) (f,g) := (ef,eg). 

(** Now we can have more coherent two-variable functors. *)

Definition fmap22 {A B C : Type} `{Is0Coh21Cat A} `{Is0Coh21Cat B} `{Is0Coh21Cat C}
  (F : A -> B -> C) `{!Is0Coh1Functor (uncurry F), !Is0Coh21Functor (uncurry F)}
  {a1 a2 : A} {b1 b2 : B} (f1 : a1 $-> a2) (f2 : b1 $-> b2) (g1 : a1 $-> a2) (g2 : b1 $-> b2)
  (alpha : f1 $== g1) (beta : f2 $== g2)
  : (fmap11 F f1 f2) $== (fmap11 F g1 g2)
  := @fmap2 _ _ _ _ _ _ (uncurry F) _ _ (a1, b1) (a2, b2) (f1, f2) (g1, g2) (alpha, beta).

Global Instance iemap11 {A B C : Type} `{HasEquivs A} `{HasEquivs B} `{HasEquivs C}
           (F : A -> B -> C) {ff1 : Is0Coh1Functor (uncurry F)}
           `{!Is0Coh21Functor (uncurry F), !Is1Coh1Functor (uncurry F)}
           {a1 a2 : A} {b1 b2 : B} (f1 : a1 $-> a2) (f2 : b1 $-> b2)
           {f1e : CatIsEquiv f1} {f2e : CatIsEquiv f2}
  : CatIsEquiv (fmap11 F f1 f2).
Proof.
  rapply (@iemap _ _ _ _ _ _ _ _ (uncurry F) _ _ _ (a1, b1) (a2, b2) (f1, f2)).
Defined.

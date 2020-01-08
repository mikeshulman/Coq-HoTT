(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.Overture.
Require Import Basics.PathGroupoids.
Require Import Basics.Notations.
Require Import Basics.Contractible.
Require Import Basics.Equivalences.
Require Import WildCat.Core.

(** ** Indexed product of categories *)

Global Instance is0coh1cat_forall (A : Type) (B : A -> Type)
  {c : forall a, Is0Coh1Cat (B a)}
  : Is0Coh1Cat (forall a, B a).
Proof.
  serapply Build_Is0Coh1Cat.
  + intros x y; exact (forall (a : A), x a $-> y a).
  + intros x a; exact (Id (x a)).
  + intros x y z f g a; exact (f a $o g a).
Defined.

Global Instance is0coh2cat_forall (A : Type) (B : A -> Type)
  {c1 : forall a, Is0Coh1Cat (B a)} {c2 : forall a, Is0Coh2Cat (B a)}
  : Is0Coh2Cat (forall a, B a).
Proof.
  serapply Build_Is0Coh2Cat.
  + intros x y; serapply Build_Is0Coh1Cat.
    - intros f g; exact (forall a, f a $== g a).
    - intros f a; apply Id.
    - intros f g h q p a; exact (p a $@ q a).
  + intros x y; serapply Build_Is0Coh1Gpd.
    intros f g p a; exact (gpd_rev (p a)).
  + intros x y z; serapply Build_Is0Coh1Functor.
    intros [a1 a2] [b1 b2] [f g] a.
    exact (f a $o@ g a).
Defined.

Global Instance is1coh1cat_forall (A : Type) (B : A -> Type)
    {c1 : forall a, Is0Coh1Cat (B a)} {c2 : forall a, Is0Coh2Cat (B a)}
    {c3 : forall a, Is1Coh1Cat (B a)}
    : Is1Coh1Cat (forall a, B a).
Proof.
  serapply Build_Is1Coh1Cat.
  + intros w x y z f g h a; apply cat_assoc.
  + intros x y f a; apply cat_idl.
  + intros x y f a; apply cat_idr.
Defined.

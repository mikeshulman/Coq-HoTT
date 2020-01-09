(* -*- mode: coq; mode: visual-line -*-  *)
Require Import Basics.
Require Import WildCat.Core.
Require Import WildCat.Equiv.

(** * Displayed wild categories *)

(* Reserved Notation "x $-[ f ]-> y" (at level 99). *)
Reserved Infix "$$o" (at level 40).
(* Reserved Notation "r $=[ p ]= s" (at level 70). *)
Reserved Notation "f ^$$" (at level 20).
Reserved Infix "$$@" (at level 30).
Reserved Infix "$$o@" (at level 30).

(** ** 0-coherent displayed 1-categories *)

Class Is0Coh1DCat {A : Type} `{Is0Coh1Cat A} (B : A -> Type) :=
{
  DHom : forall {a b : A} (f : a $-> b), B a -> B b -> Type ;
  (* where "x $-[ f ]-> y" := (DHom _ _ f x y) *)
  DId : forall {a : A} (x : B a), DHom (Id a) x x ;
  DComp : forall {a b c : A} {g : b $-> c} {f : a $-> b}
                 {x : B a} {y : B b} {z : B c},
      DHom g y z -> DHom f x y  -> DHom (g $o f) x z
}.

(* Notation "x $-[ f ]-> y" := (DHom f x y). *)
Notation "v $$o u" := (DComp v u).

Global Instance is0coh1cat_sigma {A : Type} (B : A -> Type) `{Is0Coh1DCat A B}
  : Is0Coh1Cat (sig B).
Proof.
  srapply Build_Is0Coh1Cat.
  - intros [a x] [b y]; exact {f : a $-> b & DHom f x y}.
  - cbn. intros [a x]; exact (Id a; DId x).
  - cbn. intros [a x] [b y] [c z] [g v] [f u]. exact (g $o f; v $$o u).
Defined.

Class Is0Coh1DGpd {A : Type} (B : A -> Type)
      `{Is0Coh1DCat A B} {ag : Is0Coh1Gpd A} :=
  { dgpd_rev : forall {a b : A} {f : a $-> b} {x : B a} {y : B b},
      DHom f x y -> DHom (f^$) y x }.

Notation "u ^$$" := (dgpd_rev u).

Global Instance is0coh1gpd_sigma {A : Type} (B : A -> Type) `{Is0Coh1DGpd A B}
  : Is0Coh1Gpd (sig B).
Proof.
  srapply Build_Is0Coh1Gpd.
  intros [a x] [b y] [f u].
  exact (f^$ ; u^$$).
Defined.

Class Is0Coh1DFunctor {A1 A2 : Type} (B1 : A1 -> Type) (B2 : A2 -> Type)
      `{Is0Coh1DCat A1 B1} `{Is0Coh1DCat A2 B2}
      (F : A1 -> A2) {ff : Is0Coh1Functor F}
      (G : forall a:A1, B1 a -> B2 (F a))
  := { fmapD : forall {a b : A1} {f : a $-> b} {x : B1 a} {y : B1 b},
         DHom f x y -> DHom (fmap F f) (G a x) (G b y) }.

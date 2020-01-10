(* -*- mode: coq; mode: visual-line -*-  *)
Require Import Basics.
Require Import Types.
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

Global Instance is0coh1functor_pr1 {A : Type} (B : A -> Type) `{Is0Coh1DCat A B} : Is0Coh1Functor (pr1 : (sig B) -> A).
Proof.
  apply Build_Is0Coh1Functor.
  intros [a x] [b y] [f g]; cbn.
  assumption.
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

Global Instance is0coh1functor_sigma {A1 A2 : Type} (B1 : A1 -> Type) (B2 : A2 -> Type) `{Is0Coh1DCat A1 B1} `{Is0Coh1DCat A2 B2} (F : A1 -> A2) {ff : Is0Coh1Functor F} (G : forall a:A1, B1 a -> B2 (F a)) {gg : Is0Coh1DFunctor B1 B2 F G} : Is0Coh1Functor (functor_sigma F G).
Proof.
  srapply Build_Is0Coh1Functor.
  intros [a x] [b y].
  cbn in *.
  intros [f g].
  exists (fmap F f).
  apply fmapD.
  assumption.
Defined.

Global Instance is0coh1Dcat_prod {A1 A2 : Type} `{Is0Coh1Cat A1} `{Is0Coh1Cat A2} (B1 : A1 -> Type) (B2 : A2 -> Type)  `{Is0Coh1DCat A1 B1}
      `{Is0Coh1DCat A2 B2}
  : @Is0Coh1DCat (A1 * A2) _ (fun x => (B1 (fst x)) * (B2 (snd x))).
Proof.
  srapply Build_Is0Coh1DCat; intros [a1 a2] [b1 b2]; cbn.
  - intros [f g] [x1 y1] [x2 y2].
    exact ((DHom f x1 x2) * (DHom g y1 y2)).
  - refine ((DId _), (DId _)).
  - intros [c1 c2] [g1 g2] [f1 f2] [x1 x2] [y1 y2] [z1 z2] [v1 v2] [u1 u2].
    exact (DComp v1 u1, DComp v2 u2).
Defined.

(** work in progress still breaks

Class Is0Coh2DCat {A : Type} {a01 : Is0Coh1Cat A} {a02 : Is0Coh2Cat A}
      (B : A -> Type) {ba : Is0Coh1DCat B} :=
  {
    is0coh1Dcat_DHom : forall {a b : A} {x : B a} {y : B b},
      @Is0Coh1DCat  (a $-> b) _ (fun f => DHom f x y) ;
    is0coh1Dgpd_DHom : forall {a b : A} {x : B a} {y : B b},
        @Is0Coh1DGpd (a $-> b) (fun f => DHom f x y) _ _ _ ;
    is0coh1Dfunctor_DComp : forall {a b c : A}
                                   {x : B a} {y : B b} {z : B c},
        @Is0Coh1DFunctor ((b $-> c) * (a $-> b)) (a $-> c) (fun gf => let (g,f) := gf in DHom g y z * DHom f x y) _ _ _ _ _ (uncurry (@cat_comp A _ a b c)) _
                         (fun gf => let (g,f) := gf in (fun vu => let (v,u) := vu in @DComp A _ B _ a b c g f x y z v u))
        
                         }.

*)

(** old attempt at Is0Coh2DCat
    DHom2 : forall {a b : A} {x : B a} {y : B b} {f g : a $-> b}
                   (p : f $== g), (DHom f x y) -> (DHom g x y) -> Type ;
    DHom2_rev : forall {a b : A} {x : B a} {y : B b} {f g : a $-> b}
                       (p : f $== g) (u : DHom f x y) (v : DHom g x y),
                       DHom2 p u v -> DHom2 (p ^$) v u ;
    DId2 : forall {a b : A} {x : B a} {y : B b} {f : a $-> b}
                  (u : DHom f x y), DHom2 (Id f) u u ;
    DComp2 : forall {a b c : A} {x : B a} {y : B b} {z : B c}
        {f1 f2 : a $-> b} {g1 g2 : b $-> c} (p : f1 $== f2) (q : g1 $== g2)
        (u1 : DHom f1 x y) (u2 : DHom f2 x y)
        (v1 : DHom g1 y z) (v2 : DHom g2 y z),
        (DHom2 p u1 u2) -> (DHom2 q v1 v2)
        -> (DHom2 (q $o@ p) (v1 $$o u1) (v2 $$o u2))
 *)

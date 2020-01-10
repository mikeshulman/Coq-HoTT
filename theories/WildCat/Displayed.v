(* -*- mode: coq; mode: visual-line -*-  *)
Require Import Basics.
Require Import Types.
Require Import WildCat.Core.
Require Import WildCat.Equiv.
Require Import WildCat.Opposite.

(** * Displayed wild categories *)

(* Reserved Notation "x $-[ f ]-> y" (at level 99). *)
Reserved Infix "$$o" (at level 40).
(* Reserved Notation "r $=[ p ]= s" (at level 70). *)
Reserved Notation "f ^$$" (at level 20).
Reserved Infix "$$@" (at level 30).
Reserved Infix "$$o@" (at level 30).


(** ** displayed graphs *)

Class IsDGraph {A : Type} (B : A -> Type) :=
{
  isgraph_base : IsGraph A ;
  DGraph_Hom : forall {a b : A} (f : a $-> b), B a -> B b -> Type
  (* where "x $-[ f ]-> y" := (DHom _ _ f x y) *)
}.


(** ** 0-coherent displayed 1-categories *)

Class Is0Coh1DCat {A : Type} `{Is0Coh1Cat A} (B : A -> Type) :=
{
(**  is_Dgraph : IsDGraph B; *)
  DHom : forall {a b : A} (f : a $-> b), B a -> B b -> Type ; 
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
  intros [a x] [b y] [f u]; cbn.
  assumption.
Defined.  

(** ** contravariant 0-coherent displayed 1-categories *)
Class Is_contra_0Coh1DCat {A : Type} `{Is0Coh1Cat A} (B : A -> Type) :=
{
  contra_DHom : forall {a b : A} (f : a $-> b), B b -> B a -> Type ;
  contra_DId : forall {a : A} (x : B a), contra_DHom (Id a) x x ;
  contra_DComp : forall {a b c : A} {g : b $-> c} {f : a $-> b}
                    {x : B a} {y : B b} {z : B c} ,
      contra_DHom f y x -> contra_DHom g z y -> contra_DHom (g $o f) z x
}.

Global Instance is_contra_0coh1DCat_op {A : Type} `{Is0Coh1Cat A} (B : A -> Type) `{Is_contra_0Coh1DCat A B} : @Is0Coh1DCat (A^op) _ B.
Proof.
  srapply Build_Is0Coh1DCat; unfold op in *; cbn in *.
  - intros a b.
    apply contra_DHom.
  - intros a x.
    apply contra_DId.
  - intros a b c g f x y z.
    apply contra_DComp.
Defined.

Global Instance is0coh1cat_op_sigma {A : Type} (B : A -> Type) `{Is_contra_0Coh1DCat A B}
  : Is0Coh1Cat (sig B).
Proof.
  srapply Build_Is0Coh1Cat.
  - intros [a x] [b y]; exact {f : a $-> b & contra_DHom f y x}.
  - cbn. intros [a x]; exact (Id a; contra_DId x).
  - cbn. intros [a x] [b y] [c z] [g v] [f u]. exact (g $o f; contra_DComp u v).
Defined.

Global Instance is_contra_0coh1functor_pr1 {A : Type} (B : A -> Type) `{Is_contra_0Coh1DCat A B} : Is0Coh1Functor (pr1 : (sig B) -> A).
Proof.
  apply Build_Is0Coh1Functor.
  intros [a x] [b y] [f u]; cbn.
  assumption.
Defined.  



(** 0-coherent displayed 1-groupoids *)

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

(** 0-coherent 1-displayed functors *)

Class Is0Coh1DFunctor {A1 A2 : Type} (B1 : A1 -> Type) (B2 : A2 -> Type)
      `{Is0Coh1DCat A1 B1} `{Is0Coh1DCat A2 B2}
      (F : A1 -> A2) {ff : Is0Coh1Functor F}
      (G : forall a:A1, B1 a -> B2 (F a))
  := { fmapD : forall {a b : A1} {f : a $-> b} {x : B1 a} {y : B1 b},
         DHom f x y -> DHom (fmap F f) (G a x) (G b y) }.

Arguments fmapD {A1 A2 B1 B2 _ _ _ _ F ff} G {gg a b f x y} u : rename.

Global Instance is0coh1functor_sigma {A1 A2 : Type} (B1 : A1 -> Type) (B2 : A2 -> Type) `{Is0Coh1DCat A1 B1} `{Is0Coh1DCat A2 B2} (F : A1 -> A2) {ff : Is0Coh1Functor F} (G : forall a:A1, B1 a -> B2 (F a)) {gg : Is0Coh1DFunctor B1 B2 F G} : Is0Coh1Functor (functor_sigma F G).
Proof.
  srapply Build_Is0Coh1Functor.
  intros [a x] [b y].
  cbn in *.
  intros [f g].
  exists (fmap F f).
  apply (fmapD G).
  assumption.
Defined.

(** products of 0-coherent displayed 1-categories *)

Global Instance is0coh1Dcat_prod {A1 A2 : Type} `{Is0Coh1Cat A1} `{Is0Coh1Cat A2} (B1 : A1 -> Type) (B2 : A2 -> Type)  `{!Is0Coh1DCat B1}
      `{!Is0Coh1DCat B2}
  : @Is0Coh1DCat (A1 * A2) _ (fun x => (B1 (fst x)) * (B2 (snd x))).
Proof.
  srapply Build_Is0Coh1DCat; intros [a1 a2] [b1 b2]; cbn.
  - intros [f g] [x1 y1] [x2 y2].
    exact ((DHom f x1 x2) * (DHom g y1 y2)).
  - refine ((DId _), (DId _)).
  - intros [c1 c2] [g1 g2] [f1 f2] [x1 x2] [y1 y2] [z1 z2] [v1 v2] [u1 u2].
    exact (DComp v1 u1, DComp v2 u2).
Defined.

(** comparison functors between product of sigmas and sigma of product *)
Global Instance is0coh1functor_sigma_prod {A1 A2 : Type} `{Is0Coh1Cat A1} `{Is0Coh1Cat A2} (B1 : A1 -> Type) (B2 : A2 -> Type) `{!Is0Coh1DCat B1} `{!Is0Coh1DCat B2} : @Is0Coh1Functor ((sig B1) * (sig B2)) ({ x : (A1 * A2) & (B1 (fst x)) * (B2 (snd x))}) _ _ (fun x => let (u,v) := x in ((u.1, v.1);(u.2, v.2))).
Proof.
  rapply Build_Is0Coh1Functor.
  intros [[a1 x1] [a2 x2]] [[b1 y1] [b2 y2]]; cbn in *.  
  intros [[f1 u1] [f2 u2]].
  exact ((f1, f2) ; (u1, u2)).
Defined.  

Global Instance is0coh1functor_prod_sigma {A1 A2 : Type} `{Is0Coh1Cat A1} `{Is0Coh1Cat A2} (B1 : A1 -> Type) (B2 : A2 -> Type) `{!Is0Coh1DCat B1} `{!Is0Coh1DCat B2} : @Is0Coh1Functor ({ x : (A1 * A2) & (B1 (fst x)) * (B2 (snd x))})  ((sig B1) * (sig B2)) _ _ (fun x => ((fst (pr1 x); fst (pr2 x)),(snd (pr1 x); snd (pr2 x)))).
Proof.
  rapply Build_Is0Coh1Functor.
  intros [[a1 a2] [x1 x2]] [[b1 b2] [y1 y2]]; cbn in *.  
  intros [[f1 f2] [u1 u2]].
  exact ((f1 ; u1) , (f2; u2)).
Defined.  


(** 0-coherent displayed 21-categories *)

Class Is0Coh21DCat {A : Type} {a01 : Is0Coh1Cat A} {a02 : Is0Coh21Cat A}
      (B : A -> Type) {ba : Is0Coh1DCat B} :=
  {
    is0coh1Dcat_DHom : forall {a b : A} {x : B a} {y : B b},
      @Is0Coh1DCat  (a $-> b) _ (fun f => DHom f x y) ;
    is0coh1Dgpd_DHom : forall {a b : A} {x : B a} {y : B b},
        @Is0Coh1DGpd (a $-> b) (fun f => DHom f x y) _ _ _ ;
    is0coh1Dfunctor_DComp : forall {a b c : A}
                                   {x : B a} {y : B b} {z : B c},
(@Is0Coh1DFunctor ((b $-> c) * (a $-> b)) (a $-> c)
                            (fun gf => DHom (fst gf) y z * DHom (snd gf) x y) (fun k => DHom k x z) _ (is0coh1Dcat_prod (fun g => DHom g y z) (fun f => DHom f x y) ) _ _ (uncurry (@cat_comp A _ a b c)) _                          (fun h => (fun vu => @DComp A _ B _ a b c (fst h) (snd h) x y z (fst vu) (snd vu))))
}. 

Global Existing Instance is0coh1Dcat_DHom.
Global Existing Instance is0coh1Dgpd_DHom.
Global Existing Instance is0coh1Dfunctor_DComp.

Global Instance is0coh21cat_sigma {A : Type} (B : A -> Type) `{Is0Coh1DCat A B} {ha21 : Is0Coh21Cat A} {hab : Is0Coh21DCat B}
  : Is0Coh21Cat (sig B).
Proof.
  rapply Build_Is0Coh21Cat.
  - exact _.
  - intros [a x] [b y] [c z].
    serapply Build_Is0Coh1Functor.
    intros [[g1 v1] [f1 u1]] [[g2 v2] [f2 u2]] [[q qq] [p pp]]; cbn in *.
    exists (q $o@ p).
    refine  (@fmapD   ((b $-> c) * (a $-> b)) (a $-> c) (fun gf => DHom (fst gf) y z * DHom (snd gf) x y) (fun k => DHom k x z)     _ (is0coh1Dcat_prod (fun g => DHom g y z) (fun f => DHom f x y) ) _ _
               (uncurry (@cat_comp A _ a b c)) _ (fun h => (fun vu => @DComp A _ B _ a b c (fst h) (snd h) x y z (fst vu) (snd vu)))
               (is0coh1Dfunctor_DComp) (g1, f1) (g2, f2) (q,p) (v1, u1) (v2, u2) (qq,pp)).
Defined.

Global Instance is0coh2functor_pr1 {A : Type} (B : A -> Type) `{Is0Coh21DCat A B} : Is0Coh2Functor (pr1 : (sig B) -> A).
Proof.
  apply Build_Is0Coh2Functor.
  intros [a x] [b y] [f u] [g v] [p pp]; cbn.
  assumption.
Defined.  



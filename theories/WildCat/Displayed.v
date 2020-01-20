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

(** ** displayed graphs; not used for anything because it broke *)

Class IsDGraph {A : Type} (B : A -> Type) :=
{
  isgraph_base : IsGraph A ;
  DGraph_Hom : forall {a b : A} (f : a $-> b), B a -> B b -> Type
  (* where "x $-[ f ]-> y" := (DHom _ _ f x y) *)
}.

(** ** 0-categorical displayed structures *)

(** A wild displayed (0,1)-category has 1-morphisms and operations on them, but no coherence. *)

Class Is01DCat {A : Type} `{Is01Cat A} (B : A -> Type) :=
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
                                         
Global Instance is01cat_sigma {A : Type} (B : A -> Type) `{Is01DCat A B}
  : Is01Cat (sig B).
Proof.
  srapply Build_Is01Cat.
  - intros [a x] [b y]; exact {f : a $-> b & DHom f x y}.
  - cbn. intros [a x]; exact (Id a; DId x).
  - cbn. intros [a x] [b y] [c z] [g v] [f u]. exact (g $o f; v $$o u).
Defined.

Global Instance is0functor_pr1 {A : Type} (B : A -> Type) `{Is01DCat A B} : Is0Functor (pr1 : (sig B) -> A).
Proof.
  apply Build_Is0Functor.
  intros [a x] [b y] [f u]; cbn.
  assumption.
Defined.  

(** A wild displayed 0-groupoid is a wild displayed (0,1)-category whose morphisms can be reversed. *)

Class Is0DGpd {A : Type} (B : A -> Type)
      `{Is01DCat A B} {ag : Is0Gpd A} :=
  { dgpd_rev : forall {a b : A} {f : a $-> b} {x : B a} {y : B b},
      DHom f x y -> DHom (f^$) y x }.

Notation "u ^$$" := (dgpd_rev u).

Global Instance is0gpd_sigma {A : Type} (B : A -> Type) `{Is0DGpd A B}
  : Is0Gpd (sig B).
Proof.
  srapply Build_Is0Gpd.
  intros [a x] [b y] [f u].
  exact (f^$ ; u^$$).
Defined.


(** A displayed 0-functor acts on morphisms, but satisfies no axioms. *)

Class Is0DFunctor {A1 A2 : Type} (B1 : A1 -> Type) (B2 : A2 -> Type)
      `{Is01DCat A1 B1} `{Is01DCat A2 B2}
      (F : A1 -> A2) {ff : Is0Functor F}
      (G : forall a:A1, B1 a -> B2 (F a))
  := { fmapD : forall {a b : A1} {f : a $-> b} {x : B1 a} {y : B1 b},
         DHom f x y -> DHom (fmap F f) (G a x) (G b y) }.

Arguments fmapD {A1 A2 B1 B2 _ _ _ _ F ff} G {gg a b f x y} u : rename.

Global Instance is0functor_sigma {A1 A2 : Type} (B1 : A1 -> Type) (B2 : A2 -> Type) `{Is01DCat A1 B1} `{Is01DCat A2 B2} (F : A1 -> A2) {ff : Is0Functor F} (G : forall a:A1, B1 a -> B2 (F a)) {gg : Is0DFunctor B1 B2 F G} : Is0Functor (functor_sigma F G).
Proof.
  srapply Build_Is0Functor.
  intros [a x] [b y].
  cbn in *.
  intros [f g].
  exists (fmap F f).
  apply (fmapD G).
  assumption.
Defined.

(** products of displayed (0,1)-categories *)

Global Instance is01Dcat_prod {A1 A2 : Type} `{Is01Cat A1} `{Is01Cat A2} (B1 : A1 -> Type) (B2 : A2 -> Type)  `{!Is01DCat B1}
      `{!Is01DCat B2}
  : @Is01DCat (A1 * A2) _ (fun x => (B1 (fst x)) * (B2 (snd x))).
Proof.
  srapply Build_Is01DCat; intros [a1 a2] [b1 b2]; cbn.
  - intros [f g] [x1 y1] [x2 y2].
    exact ((DHom f x1 x2) * (DHom g y1 y2)).
  - refine ((DId _), (DId _)).
  - intros [c1 c2] [g1 g2] [f1 f2] [x1 x2] [y1 y2] [z1 z2] [v1 v2] [u1 u2].
    exact (DComp v1 u1, DComp v2 u2).
Defined.

(** comparison functors between product of sigmas and sigma of product *)
Global Instance is0functor_sigma_prod {A1 A2 : Type} `{Is01Cat A1} `{Is01Cat A2} (B1 : A1 -> Type) (B2 : A2 -> Type) `{!Is01DCat B1} `{!Is01DCat B2} : @Is0Functor ((sig B1) * (sig B2)) ({ x : (A1 * A2) & (B1 (fst x)) * (B2 (snd x))}) _ _ (fun x => let (u,v) := x in ((u.1, v.1);(u.2, v.2))).
Proof.
  rapply Build_Is0Functor.
  intros [[a1 x1] [a2 x2]] [[b1 y1] [b2 y2]]; cbn in *.  
  intros [[f1 u1] [f2 u2]].
  exact ((f1, f2) ; (u1, u2)).
Defined.  

Global Instance is0functor_prod_sigma {A1 A2 : Type} `{Is01Cat A1} `{Is01Cat A2} (B1 : A1 -> Type) (B2 : A2 -> Type) `{!Is01DCat B1} `{!Is01DCat B2} : @Is0Functor ({ x : (A1 * A2) & (B1 (fst x)) * (B2 (snd x))})  ((sig B1) * (sig B2)) _ _ (fun x => ((fst (pr1 x); fst (pr2 x)),(snd (pr1 x); snd (pr2 x)))).
Proof.
  rapply Build_Is0Functor.
  intros [[a1 a2] [x1 x2]] [[b1 b2] [y1 y2]]; cbn in *.  
  intros [[f1 f2] [u1 u2]].
  exact ((f1 ; u1) , (f2; u2)).
Defined.


(** ** Wild 1-categorical structures *)

(** A wild displayed 1-category (a.k.a. (1,1)-category) has its hom-types enhanced to 0-groupoids, its composition operations to 0-functors, and its composition associative and unital up to these 2-cells. *)

Class Is1DCat {A : Type} `{!Is01Cat A} `{!Is1Cat A}
      (B : A -> Type) `{!Is01DCat B} :=  
  {
    is01Dcat_DHom : forall {a b : A} {x : B a} {y : B b},
      @Is01DCat  (a $-> b) _ (fun f => DHom f x y) ;
    isDgpd_DHom : forall {a b : A} {x : B a} {y : B b},
        @Is0DGpd (a $-> b) (fun f => DHom f x y) _ _ _ ;
    is0Dfunctor_DComp : forall {a b c : A}
                               {x : B a} {y : B b} {z : B c},
        (@Is0DFunctor ((b $-> c) * (a $-> b)) (a $-> c)
                      (fun gf => DHom (fst gf) y z * DHom (snd gf) x y)
                      (fun k => DHom k x z) _
                      (is01Dcat_prod (fun g => DHom g y z)
                                        (fun f => DHom f x y) ) _ _
                      (uncurry (@cat_comp A _ a b c)) _
                      (fun h => (fun vu =>
                                   @DComp A _ B _ a b c (fst h) (snd h)
                                          x y z (fst vu) (snd vu))));
    dcat_assoc : forall {a b c d : A}
                        {f : a $-> b} {g : b $-> c} {h : c $-> d}
                        {x : B a} {y : B b} {z : B c} {w : B d}
                        (u : DHom f x y) (v : DHom g y z) (t : DHom h z w),
        (@DHom (a $-> d) _ (fun k => DHom k x w) _
               ((h $o g) $o f) (h $o ( g $o f))
               (cat_assoc f g h) ((t $$o v) $$o u) (t $$o (v $$o u)));  
    dcat_idl : forall {a b : A} {f : a $-> b} {x : B a} {y : B b}
                      (u : DHom f x y),
        @DHom (a $-> b) _ (fun k => DHom k x y) _
              ((Id b) $o f) f (cat_idl f) ((DId y) $$o u) u ;
    dcat_idr : forall {a b : A} {f : a $-> b} {x : B a} {y : B b}
                      (u : DHom f x y),
        @DHom (a $-> b) _ (fun k => DHom k x y) _
              (f $o (Id a)) f (cat_idr f) (u $$o (DId x)) u
  }.


Global Existing Instance is01Dcat_DHom.
Global Existing Instance isDgpd_DHom.
Global Existing Instance is0Dfunctor_DComp.


Arguments dcat_assoc {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} u v t.
Arguments dcat_idl {_ _ _ _ _ _ _ _ _ _ _} u.
Arguments dcat_idr {_ _ _ _ _ _ _ _ _ _ _} u.


Definition DHom2  {A : Type} {a01 : Is01Cat A} {a11 : Is1Cat A} {B : A -> Type} {b01 : Is01DCat B} {b11 : Is1DCat B} {a b : A} {x : B a} {y : B b} {f : a $-> b} {g : a $-> b} (p : f $== g) (u : DHom f x y) (v : DHom g x y) : Type := DHom  p u v.

Definition DComp2 {A} {a01 : Is01Cat A} {a11 : Is1Cat A} {B : A -> Type} {b01 : Is01DCat B} {b11 : Is1DCat B} {a b c : A} {x : B a} {y : B b} {z : B c} {f1 : a $-> b} {f2 : a $-> b} {g1 : b $-> c} {g2 : b $-> c} {p : f1 $== f2} {q : g1 $== g2} {u1 : DHom f1 x y} {u2 : DHom f2 x y} {v1 : DHom g1 y z} {v2 : DHom g2 y z} (qq : DHom2 q v1 v2) (pp : DHom2 p u1 u2) : DHom2 (q $o@ p) (v1 $$o u1) (v2 $$o u2)
        := (@fmapD   ((b $-> c) * (a $-> b)) (a $-> c) (fun gf => DHom (fst gf) y z * DHom (snd gf) x y) (fun k => DHom k x z)     _ (is01Dcat_prod (fun g => DHom g y z) (fun f => DHom f x y) ) _ _
               (uncurry (@cat_comp A _ a b c)) _ (fun h => (fun vu => @DComp A _ B _ a b c (fst h) (snd h) x y z (fst vu) (snd vu)))
               (is0Dfunctor_DComp) (g1, f1) (g2, f2) (q,p) (v1, u1) (v2, u2) (qq,pp)).

Arguments DComp2 {A _ _ B _ _ a b c x y z f1 f2 g1 g2 p q u1 u2 v1 v2} qq pp.

Definition  dcat_assoc_opp {A : Type} `{!Is01Cat A} `{!Is1Cat A} (B : A -> Type) `{!Is01DCat B} `{!Is1DCat B}
            {a b c d : A} {f : a $-> b} {g : b $-> c} {h : c $-> d} {x : B a} {y : B b} {z : B c} {w : B d} (u : DHom f x y) (v : DHom g y z) (t : DHom h z w) : (DHom2 ((cat_assoc f g h)^$) (t $$o (v $$o u)) ((t $$o v) $$o u)) := ((dcat_assoc u v t)^$$).  

Arguments dcat_assoc_opp {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} u v t.

(** products of displayed 1-categories *)

Global Instance is1Dcat_prod {A1 A2 : Type} `{!Is01Cat A1} `{!Is1Cat A1} `{!Is01Cat A2} `{!Is1Cat A2} (B1 : A1 -> Type) (B2 : A2 -> Type)  `{!Is01DCat B1}
      `{!Is01DCat B2} `{!Is1DCat B1} `{!Is1DCat B2}
  : @Is1DCat (A1 * A2) _  _ (fun x => (B1 (fst x)) * (B2 (snd x))) _.
Proof.
  serapply Build_Is1DCat; intros [a1 a2] [b1 b2].
  - intros [x1 x2] [y1 y2]; cbn in *.
    serapply Build_Is01DCat.
    + intros [f1 f2] [g1 g2] [p q] [u1 u2] [v1 v2]; cbn in *.
      exact ((DHom2 p u1 v1) * (DHom2 q u2 v2)).
    + intros [f1 f2] [u1 u2]; cbn in *.
      exact ((@DId (a1 $-> b1) _ (fun k => DHom k x1 y1) _ f1 u1),
             (@DId (a2 $-> b2) _ (fun k => DHom k x2 y2) _ f2 u2)).
    + intros [f1 f2] [g1 g2] [h1 h2] [q1 q2] [p1 p2] [u1 u2] [v1 v2] [w1 w2] [qq1 qq2] [pp1 pp2]; cbn in *.
      exact (DComp qq1 pp1, DComp qq2 pp2).
  - intros [x1 x2] [y1 y2]; cbn in *.
    apply Build_Is0DGpd.
    intros [f1 f2] [g1 g2] [p q] [u1 u2] [v1 v2] [pp qq]; cbn in *.
    exact (dgpd_rev pp, dgpd_rev qq).
  - intros [c1 c2] [x1 x2] [y1 y2] [z1 z2].
    apply Build_Is0DFunctor.
    intros [[h1 h2] [f1 f2]] [[k1 k2] [g1 g2]] [[q1 q2] [p1 p2]].
    intros [[s1 s2] [u1 u2]] [[t1 t2] [v1 v2]] [[qq1 qq2] [pp1 pp2]]; cbn in *.
    exact (DComp2 qq1 pp1, DComp2 qq2 pp2).
  - intros [c1 c2] [d1 d2] [f1 f2] [g1 g2] [h1 h2]; cbn in *.
    intros [x1 x2] [y1 y2] [z1 z2] [w1 w2] [u1 u2] [v1 v2] [t1 t2].
    exact (dcat_assoc u1 v1 t1, dcat_assoc u2 v2 t2).
  - intros [f1 f2] [x1 x2] [y1 y2] [u1 u2].
    exact (dcat_idl u1, dcat_idl u2).
  - intros [f1 f2] [x1 x2] [y1 y2] [u1 u2].
    exact (dcat_idr u1, dcat_idr u2).
Defined.

(* broken proofs

Global Instance is1cat_sigma {A : Type} (B : A -> Type) `{Is1DCat A B} 
  : Is1Cat (sig B).
Proof.
  rapply Build_Is1Cat.
  - intros [a x] [b y] [c z].
    serapply Build_Is0Functor.
    intros [[g1 v1] [f1 u1]] [[g2 v2] [f2 u2]]; cbn in *.
    intros [ppp qqq]; cbn in *.
    
    exists ((pr1 qqq) $o@ (pr1 ppp)).
    exact (DComp2 (pr2 qqq) (pr2 ppp)).

    intros 
    intros [a x] [b y] [c z] [d w] [f u] [g v] [h t]; cbn in *.
    exact (cat_assoc f g h ; dcat_assoc u v t).
  - intros [a x] [b y] [f u]; cbn in *.
    exact (cat_idl f ; dcat_idl u).
  - intros [a x] [b y] [f u].
    exact (cat_idr f ; dcat_idr u).
Defined.


Global Instance is1coh1functor_pr1 {A : Type} (B : A -> Type) `{Is1DCat A B} : Is1Functor (pr1 : (sig B) -> A).
Proof.
  apply Build_Is1Functor.
  - intros [a x] [b y] [f u] [g v]; cbn.
    intros p.
    exact (pr1 p).
    apply Id.
  - intros [a x] [b y] [c z] [f u] [g v]; cbn.
    apply Id.
Defined.


Global Instance is1cat_sigma {A : Type} (B : A -> Type) `{Is01DCat A B} {ha21 : Is0Coh21Cat A} {hab : Is0Coh21DCat B}
  : Is0Coh21Cat (sig B).
Proof.
  rapply Build_Is0Coh21Cat.
  - exact _.
  - intros [a x] [b y] [c z].
    serapply Build_Is0Functor.
    intros [[g1 v1] [f1 u1]] [[g2 v2] [f2 u2]] [[q qq] [p pp]]; cbn in *.
    exists (q $o@ p).
    exact (DComp2 qq pp).
Defined.

Global Instance is0coh2functor_pr1 {A : Type} (B : A -> Type) `{Is0Coh21DCat A B} : Is0Coh21Functor (pr1 : (sig B) -> A).
Proof.
  apply Build_Is0Coh21Functor.
  intros [a x] [b y] [f u] [g v] [p pp]; cbn.
  assumption.
Defined.  
*)


(** A displayed 1-functor acts on 2-cells (satisfying no axioms) and also preserves composition and identities up to a 2-cell. *)

Class Is1DFunctor  {A1 A2 : Type} (B1 : A1 -> Type) (B2 : A2 -> Type)
  `{!Is01Cat A1} `{!Is01Cat A2}   `{!Is1Cat A1} `{!Is1Cat A2} `{!Is01DCat B1} `{!Is01DCat B2} `{!Is1DCat B1} `{!Is1DCat B2}
      (F : A1 -> A2) `{!Is0Functor F} `{!Is1Functor F}
      (G : forall a:A1, B1 a -> B2 (F a)) `{!Is0DFunctor B1 B2 F G} 
  := {
      fmapD2 : forall {a b : A1} {f g : a $-> b} {x : B1 a} {y : B1 b}
                      (u : DHom f x y) (v : DHom g x y) (p : f $== g),
        DHom2 p u v -> DHom2 (fmap2 F p) (fmapD G u) (fmapD G v) ;
      fmapD_id : forall {a : A1} {x : B1 a}, DHom2 (fmap_id F a) (fmapD G (DId x)) ( DId (G a x));
      fmapD_comp : forall {a b c : A1} {f : a $-> b} {g : b $-> c} {x : B1 a} {y : B1 b} {z : B1 c} (u : DHom f x y) (v : DHom g y z), DHom2 (fmap_comp F f g) (fmapD G (DComp v u)) (DComp (fmapD G v) (fmapD G u)) 
                             
    }.

Arguments fmapD2 {A1 A2 B1 B2 _ _ _ _ _ _ _ _ F _ _ G _ _ a b f g x y} u v p.
Arguments fmapD_id {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ } x.
Arguments fmapD_comp {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a b c f g x y z} u v.

(* requires the is1cat_sigma proof

Global Instance is1functor_sigma {A1 A2 : Type} (B1 : A1 -> Type) (B2 : A2 -> Type)
         `{!Is01Cat A1} `{!Is01Cat A2}   `{!Is1Cat A1} `{!Is1Cat A2} `{!Is01DCat B1} `{!Is01DCat B2} `{!Is1DCat B1} `{!Is1DCat B2}
      (F : A1 -> A2) `{!Is0Functor F} `{!Is1Functor F}
      (G : forall a:A1, B1 a -> B2 (F a)) `{!Is0DFunctor B1 B2 F G}
   `{!Is1DFunctor B1 B2 F G}  : Is1Functor (functor_sigma F G). 
*)


(* old 

Global Instance is0coh21functor_sigma  {A1 A2 : Type} (B1 : A1 -> Type) (B2 : A2 -> Type)
        {HA1 : Is01Cat A1} {HA21 : Is0Coh21Cat A1} {HA2 : Is01Cat A2} {HA22 : Is0Coh21Cat A2} {HB1 : Is01DCat B1} {HB2 : Is01DCat B2} {ab1 : Is0Coh21DCat B1} {ab2 : Is0Coh21DCat B2}
      (F : A1 -> A2) `{!Is0Functor F} `{!Is0Coh21Functor F}
      (G : forall a:A1, B1 a -> B2 (F a)) 
      `{!Is0Coh1DFunctor B1 B2 F G} `{!Is0Coh21DFunctor B1 B2 F G} : Is0Coh21Functor (functor_sigma F G).
Proof.
  srapply Build_Is0Coh21Functor.
  intros [a x] [b y] [f u] [g v] [p pp].
  cbn in *.
  exact (fmap2 F p ; fmapD2 u v p pp).
Defined.


Global Instance is1coh1functor_sigma  {A1 A2 : Type} (B1 : A1 -> Type) (B2 : A2 -> Type)
             {HA1 : Is01Cat A1} {HA12 : Is0Coh21Cat A1} {HA11 : Is1Coh1Cat A1} {HA2 : Is01Cat A2} {HA22 : Is0Coh21Cat A2} {HA21 : Is1Coh1Cat A2} {HB1 : Is01DCat B1} {HB2 : Is01DCat B2} {ab1 : Is0Coh21DCat B1} {ab2 : Is0Coh21DCat B2} {ab11 : Is1Coh1DCat B1} {ab21 : Is1Coh1DCat B2}
      (F : A1 -> A2) `{!Is0Functor F} `{!Is0Coh21Functor F} `{!Is1Coh1Functor F}
      (G : forall a:A1, B1 a -> B2 (F a)) 
      `{!Is0Coh1DFunctor B1 B2 F G} `{!Is0Coh21DFunctor B1 B2 F G}
      `{!Is1Coh1DFunctor B1 B2 F G} : Is1Coh1Functor (functor_sigma F G).
Proof.
  srapply Build_Is1Coh1Functor.
  - intros [a x]; cbn.
    exact (fmap_id F a ; fmapD_id x).
  - intros [a x] [b y] [c z] [f u] [g v].
    exact (fmap_comp F f g ; fmapD_comp u v).
Defined.

 *)

(** TODO strong versions of the above *)


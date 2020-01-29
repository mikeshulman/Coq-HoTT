(* -*- mode: coq; mode: visual-line -*-  *)
Require Import Basics.
Require Import Types.
Require Import WildCat.Core.
Require Import WildCat.Equiv.
Require Import WildCat.Opposite.
Require Import WildCat.Prod.

(** * Displayed wild categories *)

(* Reserved Notation "x $-[ f ]-> y" (at level 99). *)
Reserved Infix "$$o" (at level 40).
(* Reserved Notation "r $=[ p ]= s" (at level 70). *)
Reserved Notation "f ^$$" (at level 20).
Reserved Infix "$$@" (at level 30).
Reserved Infix "$$o@" (at level 30).

Class IsDGraph {A : Type} (B : A -> Type) `{IsGraph A} :=
{
  dHom : forall {a b : A} (f : a $-> b), B a -> B b -> Type
}.
(* Notation "x $-[ f ]-> y" := (dHom f x y). *)

(** ** 0-categorical displayed structures *)

(** A wild displayed (0,1)-category has 1-morphisms and operations on them, but no coherence. *)

Arguments dHom {_ _ _ _ a b} f x y.

Class Is01DCat {A : Type} `{Is01Cat A} (B : A -> Type) `{!IsDGraph B} :=
{
  dId : forall {a : A} (x : B a), dHom (Id a) x x;
  dcat_comp : forall {a b c : A} {g : b $-> c} {f : a $-> b}
                 {x : B a} {y : B b} {z : B c},
      dHom g y z -> dHom f x y  -> dHom (g $o f) x z
}.

Notation "v $$o u" := (dcat_comp v u).

Definition dcat_postcomp {A} `{Is01Cat A} (B : A -> Type) `{!IsDGraph B} `{!Is01DCat B} {a b c : A} (x : B a) {y : B b} {z : B c} (f : a $-> b) {g : b $-> c} (v : dHom g y z)
  : (dHom f x y) -> (dHom (g $o f) x z)
  := fun u => v $$o u.

Definition dcat_precomp {A} `{Is01Cat A} (B : A -> Type) `{!IsDGraph B} `{!Is01DCat B} {a b c : A} {x : B a} {y : B b} (z : B c) {f : a $-> b} (g : b $-> c) (u : dHom f x y)
  : (dHom g y z) -> (dHom (g $o f) x z)
  := fun v => v $$o u.

Print Is01DCat.
Print IsDGraph.
Check Build_IsDGraph.

(*
Definition Build_Is01DCat {A : Type} {ha: Is01Cat A} (B : A -> Type)
           (dHom' :  forall {a b : A} (f : a $-> b), B a -> B b -> Type)
           (dId' : forall {a : A} (x : B a), dHom' (Id a) x x)
           (dcat_comp' : forall {a b c : A} {g : b $-> c} {f : a $-> b}
                 {x : B a} {y : B b} {z : B c},
               dHom' g y z -> dHom' f x y  -> dHom' (g $o f) x z) :
  (@Is01DCat A ha B (Build_IsDGraph A B _ (fun a b => (fun f x y => @dHom' a b f x y )))).
Proof.
  apply Build_Is01DCat'.
  - apply dId'.
  - apply dcat_comp'.
Defined.
*)
    
Global Instance is01cat_sigma {A : Type} (B : A -> Type) `{Is01DCat A B}
  : Is01Cat (sig B).
Proof.
  srapply Build_Is01Cat.
  - intros [a x] [b y]; exact {f : a $-> b & dHom f x y}.
  - cbn. intros [a x]; exact (Id a; dId x).
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
      dHom f x y -> dHom (f^$) y x }.

Notation "u ^$$" := (dgpd_rev u).

Definition dGpdHom {A} {B : A -> Type} `{Is0DGpd A B} {a b : A} (f : a $-> b) (x : B a) (y : B b) := dHom f x y.

(* gpd_comp is in diagrammatic order so I had to make the same choice here *)
Definition dgpd_comp {A} {B : A -> Type} `{Is0DGpd A B} {a b c : A} {g : b $== c} {f : a $== b} {x : B a} {y : B b} {z : B c}
  : dGpdHom f x y -> dGpdHom g y z -> dGpdHom (f $@ g) x z
  := fun u v => v $$o u.
Infix "$$@" := dgpd_comp.

Definition dGpdHom_path {A} (B : A -> Type) `{Is0DGpd A B} {a b : A} (p : a = b) (x : B a) (y : B b) (q : (transport B p x) = y) : dGpdHom  (GpdHom_path p) x y.
Proof.
  destruct p, q.
  unfold GpdHom_path.
  refine (transport (fun y => (dGpdHom (Id a) x y)) ((transport_1 B x)^) _).
  apply dId.
Defined.

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
      (F : A1 -> A2) `{!Is0Functor F}
      (G : forall a:A1, B1 a -> B2 (F a))
  := { fmapd : forall {a b : A1} {f : a $-> b} {x : B1 a} {y : B1 b},
         dHom f x y -> dHom (fmap F f) (G a x) (G b y) }.

Arguments fmapd {A1 A2 B1 B2 _ _ _ _ _ _ F _} G {_ a b f x y} u : rename.

Global Instance is0functor_sigma {A1 A2 : Type} (B1 : A1 -> Type) (B2 : A2 -> Type) `{Is01DCat A1 B1} `{Is01DCat A2 B2} (F : A1 -> A2) {ff : Is0Functor F} (G : forall a:A1, B1 a -> B2 (F a)) {gg : Is0DFunctor B1 B2 F G} : Is0Functor (functor_sigma F G).
Proof.
  srapply Build_Is0Functor.
  intros [a x] [b y].
  cbn in *.
  intros [f g].
  exists (fmap F f).
  apply (fmapd G).
  assumption.
Defined.

(** ** Wild 1-categorical structures *)

(** A wild displayed 1-category (a.k.a. (1,1)-category) has its hom-types enhanced to 0-groupoids, its composition operations to 0-functors, and its composition associative and unital up to these 2-cells. *)

Class Is1DCat {A : Type} 
      (B : A -> Type) `{Is01DCat A B} `{!Is1Cat A} :=  
  {
    isdgraph_dHom : forall {a b : A} {x : B a} {y : B b},
      @IsDGraph (a $-> b) (fun f => dHom f x y) _;
    is01dcat_dHom : forall {a b : A} {x : B a} {y : B b},
      @Is01DCat  (a $-> b) _ (fun f => dHom f x y) _;
    isdgpd_dHom : forall {a b : A} {x : B a} {y : B b},
        @Is0DGpd (a $-> b) (fun f => dHom f x y) _ _ _ _;
    is0dfunctor_dcat_postcomp : forall {a b c : A} (x : B a) {y : B b} {z : B c}
                                  (f : a $-> b) {g : b $-> c}
                                  (v : dHom g y z),
        (@Is0DFunctor _ _ (fun ff => dHom ff x y) (fun h => dHom h x z) _ _ _ _ _ _ (cat_postcomp a g) _ (fun fff => dcat_postcomp B x fff v)) ;
    is0dfunctor_dcat_precomp : forall {a b c : A} {x : B a} {y : B b} (z : B c)
                                 {f : a $-> b} (g : b $-> c)
                                 (u : dHom f x y),
        (@Is0DFunctor _ _ (fun gg => dHom gg y z) (fun h => dHom h x z) _ _ _ _ _ _ (cat_precomp c f) _ (fun ggg => dcat_precomp B z ggg u)) ;
(*  is0Dfunctor_dcat_comp : forall {a b c : A}
                               {x : B a} {y : B b} {z : B c},
        (@Is0DFunctor ((b $-> c) * (a $-> b)) (a $-> c)
                      (fun gf => dHom (fst gf) y z * dHom (snd gf) x y)
                      (fun k => dHom k x z) _ _
                      (is01Dcat_prod (fun g => dHom g y z)
                                        (fun f => dHom f x y) ) _ _ _
                      (uncurry (@cat_comp A _ a b c)) _
                      (fun h => (fun vu =>
                                   @dcat_comp A _ B _ _ a b c (fst h) (snd h)
                                          x y z (fst vu) (snd vu)))); *)
    dcat_assoc : forall {a b c d : A}
                        {f : a $-> b} {g : b $-> c} {h : c $-> d}
                        {x : B a} {y : B b} {z : B c} {w : B d}
                        (u : dHom f x y) (v : dHom g y z) (t : dHom h z w),
        (@dHom (a $-> d) (fun k => dHom k x w) _ _
               ((h $o g) $o f) (h $o ( g $o f))
               (cat_assoc f g h) ((t $$o v) $$o u) (t $$o (v $$o u)));  
    dcat_idl : forall {a b : A} {f : a $-> b} {x : B a} {y : B b}
                      (u : dHom f x y),
        @dHom (a $-> b) (fun k => dHom k x y) _ _
              ((Id b) $o f) f (cat_idl f) ((dId y) $$o u) u ;
    dcat_idr : forall {a b : A} {f : a $-> b} {x : B a} {y : B b}
                      (u : dHom f x y),
        @dHom (a $-> b) (fun k => dHom k x y) _ _
              (f $o (Id a)) f (cat_idr f) (u $$o (dId x)) u
  }.

Global Existing Instance isdgraph_dHom.
Global Existing Instance is01dcat_dHom.
Global Existing Instance isdgpd_dHom.
Global Existing Instance is0dfunctor_dcat_postcomp.
Global Existing Instance is0dfunctor_dcat_precomp.
(* Global Existing Instance is0dfunctor_dcat_comp. *)

Arguments dcat_assoc {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} u v t.
Arguments dcat_idl {_ _ _ _ _ _ _ _ _ _ _ _} u.
Arguments dcat_idr {_ _ _ _  _ _ _ _ _ _ _ _} u.

Definition  dcat_assoc_opp  {A : Type} (B : A -> Type) `{Is01DCat A B} `{!Is1Cat A} `{! Is1DCat B}
            {a b c d : A} {f : a $-> b} {g : b $-> c} {h : c $-> d}
            {x : B a} {y : B b} {z : B c} {w : B d}
            (u : dHom f x y) (v : dHom g y z) (t : dHom h z w) : (@dHom (a $-> d) (fun k => dHom k x w) _ _ (h $o (g $o f)) ((h $o g) $o f) ((cat_assoc f g h)^$) (t $$o (v $$o u)) ((t $$o v) $$o u)) := ((dcat_assoc u v t)^$$).  

Arguments dcat_assoc_opp {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} u v t.

Definition dHom2  {A : Type} {a01 : Is01Cat A} {a11 : Is1Cat A} {B : A -> Type} {b00 : IsDGraph B} {b01 : Is01DCat B} {b11 : Is1DCat B} {a b : A} {x : B a} {y : B b} {f : a $-> b} {g : a $-> b} (p : f $== g) (u : dHom f x y) (v : dHom g x y) : Type := dHom  p u v.


Definition dcat_postwhisker  {A : Type} {a01 : Is01Cat A} {a11 : Is1Cat A} {B : A -> Type} {b00 : IsDGraph B} {b01 : Is01DCat B} {b11 : Is1DCat B}
          {a b c : A} {x : B a} {y : B b} {z : B c}
           {f g : a $-> b} {u : dHom f x y} {v : dHom g x y} {h : b $-> c} (w : dHom h y z) {p : f $== g} (pp : dHom2 p u v)
  : dHom2 (cat_postwhisker h p) (w $$o u) (w $$o v).
Proof.
  Print fmapd.
  apply (@fmapd _ _ (fun ff => dHom ff x y) (fun hh => dHom hh x z) _ _ _ _ _ _  (cat_postcomp a h) _ (fun fff => dcat_postcomp B x fff w)).
  - apply is0dfunctor_dcat_postcomp; assumption. 
  - assumption.
Defined.

Arguments dcat_postwhisker {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} w {_} pp.

(* Notation "w $$@L pp" := (dcat_postwhisker w pp). *)


Definition dcat_prewhisker  {A : Type} {a01 : Is01Cat A} {a11 : Is1Cat A} {B : A -> Type} {b00 : IsDGraph B} {b01 : Is01DCat B} {b11 : Is1DCat B}
          {a b c : A} {x : B a} {y : B b} {z : B c}
           {f : a $-> b} (u : dHom f x y) {g h : b $-> c} {v : dHom g y z}  {w : dHom h y z} {q : g $== h} (qq : dHom2 q v w)
  : dHom2 (cat_prewhisker q f) (v $$o u) (w $$o u).
Proof.
  Print fmapd.
  apply (@fmapd _ _ (fun gg => dHom gg y z) (fun hh => dHom hh x z) _ _ _ _ _ _  (cat_precomp c f) _ (fun fff => dcat_precomp B z fff u)).
  - apply is0dfunctor_dcat_precomp; assumption. 
  - assumption.
Defined.

Arguments dcat_prewhisker {_ _ _ _ _ _ _ _ _ _ _ _ _ _} u {_ _ _ _ _} qq.

(* Notation "qq $$@R u" := (dcat_postwhisker u pp). *)


(*
Definition dcat_comp2 {A} {a01 : Is01Cat A} {a11 : Is1Cat A} {B : A -> Type} {b00 : IsDGraph B} {b01 : Is01DCat B} {b11 : Is1DCat B} {a b c : A} {x : B a} {y : B b} {z : B c} {f1 : a $-> b} {f2 : a $-> b} {g1 : b $-> c} {g2 : b $-> c} {p : f1 $== f2} {q : g1 $== g2} {u1 : dHom f1 x y} {u2 : dHom f2 x y} {v1 : dHom g1 y z} {v2 : dHom g2 y z} (qq : dHom2 q v1 v2) (pp : dHom2 p u1 u2) : dHom2 (q $o@ p) (v1 $$o u1) (v2 $$o u2)
        := (@fmapd   ((b $-> c) * (a $-> b)) (a $-> c) (fun gf => dHom (fst gf) y z * dHom (snd gf) x y) (fun k => dHom k x z)     _ (is01Dcat_prod (fun g => dHom g y z) (fun f => dHom f x y) ) _ _
               (uncurry (@cat_comp A _ a b c)) _ (fun h => (fun vu => @dcat_comp A _ B _ a b c (fst h) (snd h) x y z (fst vu) (snd vu)))
               (is0Dfunctor_dcat_comp) (g1, f1) (g2, f2) (q,p) (v1, u1) (v2, u2) (qq,pp)).

Arguments dcat_comp2 {A _ _ B _ _ a b c x y z f1 f2 g1 g2 p q u1 u2 v1 v2} qq pp.
*)

Global Instance is1cat_sigma {A : Type} (B : A -> Type) `{Is1DCat A B} 
  : Is1Cat (sig B).
Proof.
  serapply Build_Is1Cat.
  - intros [a x] [b y].
    serapply Build_Is01Cat.
    + intros [f u] [g v].
      exact { p : f $== g & (dHom2 p u v)}.
    + intros [f u].
      exists (Id f).
      apply  is01dcat_dHom.
    + intros [f u] [g v] [h w] [q qq] [p pp].
      exists (q $o p).
      Print dcat_comp.
      apply (@dcat_comp _ _ _ _ _ f g h q p u v w qq pp).
  - intros [a x] [b y].
    apply Build_Is0Gpd.
    intros [f u] [g v] [p pp].
    exact (p^$ ; pp^$$).
  - intros [a x] [b y] [c z] [g v].
    apply Build_Is0Functor.
    intros [f1 u1] [f2 u2] [p pp]; cbn in *.
    exact (g $@L p ; dcat_postwhisker v pp).
  - intros [a x] [b y] [c z] [f u].
    apply Build_Is0Functor.
    intros [g v] [h w] [q qq]; cbn in *.
    exact (q $@R f ; dcat_prewhisker u qq).
  - intros [a x] [b y] [c z] [d w] [f u] [g v] [h t]; cbn in *.
    exact (cat_assoc f g h ; dcat_assoc u v t).
  - intros [a x] [b y] [f u]; cbn in *.
    exact (cat_idl f ; dcat_idl u).
  - intros [a x] [b y] [f u].
    exact (cat_idr f ; dcat_idr u).
Defined.

Global Instance is1functor_pr1 {A : Type} (B : A -> Type) `{Is1DCat A B} : Is1Functor (pr1 : (sig B) -> A).
Proof.
  apply Build_Is1Functor.
  - intros [a x] [b y] [f u] [g v]; cbn.
    intros [p pp].
    exact p.
  - intros [a x]; cbn.
    apply Id.
  - intros [a x] [b y] [c z] [f u] [g v]; cbn.
    apply Id.
Defined.
                                           
(** Often, the coherences in both the base and the fiber are actually equalities rather than homotopies. *)

Class Is1DCat_Strong {A : Type} 
      (B : A -> Type) `{Is01DCat A B} `{!Is1Cat_Strong A} :=  
  {
    isdgraph_dHom_strong : forall {a b : A} {x : B a} {y : B b},
      @IsDGraph (a $-> b) (fun f => dHom f x y) _;
    is01dcat_dHom_strong : forall {a b : A} {x : B a} {y : B b},
      @Is01DCat  (a $-> b) _ (fun f => dHom f x y) _;
    isdgpd_dHom_strong : forall {a b : A} {x : B a} {y : B b},
        @Is0DGpd (a $-> b) (fun f => dHom f x y) _ _ _ _;
    is0dfunctor_dcat_postcomp_strong : forall {a b c : A} (x : B a) {y : B b} {z : B c}
                                  (f : a $-> b) {g : b $-> c}
                                  (v : dHom g y z),
        (@Is0DFunctor _ _ (fun ff => dHom ff x y) (fun h => dHom h x z) _ _ _ _ _ _ (cat_postcomp a g) _ (fun fff => dcat_postcomp B x fff v)) ;
    is0dfunctor_dcat_precomp_strong : forall {a b c : A} {x : B a} {y : B b} (z : B c)
                                 {f : a $-> b} (g : b $-> c)
                                 (u : dHom f x y),
        (@Is0DFunctor _ _ (fun gg => dHom gg y z) (fun h => dHom h x z) _ _ _ _ _ _ (cat_precomp c f) _ (fun ggg => dcat_precomp B z ggg u)) ;
    dcat_assoc_strong : forall {a b c d : A}
                        {f : a $-> b} {g : b $-> c} {h : c $-> d}
                        {x : B a} {y : B b} {z : B c} {w : B d}
                        (u : dHom f x y) (v : dHom g y z) (t : dHom h z w),
        (transport (fun k => dHom k x w) (cat_assoc_strong f g h) ((t $$o v) $$o u)) = (t $$o (v $$o u)); 
    dcat_idl_strong : forall {a b : A} {f : a $-> b} {x : B a} {y : B b}
                      (u : dHom f x y),
        (transport (fun k => dHom k x y) (cat_idl_strong f)  ((dId y) $$o u)) = u ;
    dcat_idr_strong : forall {a b : A} {f : a $-> b} {x : B a} {y : B b}
                      (u : dHom f x y),
        (transport (fun k => dHom k x y) (cat_idr_strong f) (u $$o (dId x))) = u
  }.

Global Existing Instance isdgraph_dHom_strong.
Global Existing Instance is01dcat_dHom_strong.
Global Existing Instance isdgpd_dHom_strong.
Global Existing Instance is0dfunctor_dcat_postcomp_strong.
Global Existing Instance is0dfunctor_dcat_precomp_strong.


Arguments dcat_assoc_strong {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} u v t.
Arguments dcat_idl_strong {_ _ _ _ _ _ _ _ _ _ _ _} u.
Arguments dcat_idr_strong {_ _ _ _  _ _ _ _ _ _ _ _} u.


Definition  dcat_assoc_opp_strong  {A : Type} (B : A -> Type) `{Is01DCat A B} `{!Is1Cat_Strong A} `{! Is1DCat_Strong B}
            {a b c d : A} {f : a $-> b} {g : b $-> c} {h : c $-> d}
            {x : B a} {y : B b} {z : B c} {w : B d}
            (u : dHom f x y) (v : dHom g y z) (t : dHom h z w) :
  (transport (fun k => dHom k x w) (cat_assoc_opp_strong f g h) (t $$o (v $$o u))) = ((t $$o v) $$o u).
Proof.
  unfold cat_assoc_opp_strong.
  apply (moveR_transport_V (fun k => dHom k x w) (cat_assoc_strong f g h) _ _).
  exact ((dcat_assoc_strong u v t)^).
Defined.

Arguments dcat_assoc_opp_strong {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} u v t.

Global Instance is1dcat_is1dcat_strong {A : Type} (B : A -> Type) `{Is1DCat_Strong A B} : Is1DCat B.
Proof.
  srefine (Build_Is1DCat A B _ _ _ _ _ _ _ _ _ _ _ _).
  all:intros a b.
  - intros x y ; apply isdgraph_dHom_strong.
  - intros x y ; apply is01dcat_dHom_strong.
  - intros x y ; apply isdgpd_dHom_strong.
  - intros c x y z; apply is0dfunctor_dcat_postcomp_strong.
  - intros c x y z; apply is0dfunctor_dcat_precomp_strong.
  - intros c d f g h x y z w u v t; cbn in *.
    exact (dGpdHom_path (fun k => dHom k x w) (cat_assoc_strong f g h) ((t $$o v) $$o u) (t $$o (v $$o u)) (dcat_assoc_strong u v t)).
  - intros f x y u; cbn in *.
    exact (dGpdHom_path (fun k => dHom k x y) (cat_idl_strong f) (dId y $$o u) u (dcat_idl_strong u)).
  - intros f x y u. 
    exact (dGpdHom_path (fun k => dHom k x y) (cat_idr_strong f) (u $$o dId x) u (dcat_idr_strong u)).
Defined.

(** A displayed 1-functor acts on 2-cells (satisfying no axioms) and also preserves composition and identities up to a 2-cell. *)

Class Is1DFunctor {A1 A2 : Type} (B1 : A1 -> Type) (B2 : A2 -> Type)
      `{Is1DCat A1 B1} `{Is1DCat A2 B2} (F : A1 -> A2)
      `{!Is0Functor F} `{!Is1Functor F} (G : forall a:A1, B1 a -> B2 (F a)) `{!Is0DFunctor B1 B2 F G}
  := {
      fmapd2 : forall {a b : A1} {f g : a $-> b} {x : B1 a} {y : B1 b}
                      (u : dHom f x y) (v : dHom g x y) (p : f $== g),
        dHom2 p u v -> dHom2 (fmap2 F p) (fmapd G u) (fmapd G v) ;
      fmapd_id : forall {a : A1} {x : B1 a}, dHom2 (fmap_id F a) (fmapd G (dId x)) ( dId (G a x)) ;
      fmapd_comp : forall {a b c : A1} {f : a $-> b} {g : b $-> c}
                          {x : B1 a} {y : B1 b} {z : B1 c}
                          (u : dHom f x y) (v : dHom g y z),
          dHom2 (fmap_comp F f g) (fmapd G (dcat_comp v u))
                (dcat_comp (fmapd G v) (fmapd G u))
    }.

Arguments fmapd2 {A1 A2 B1 B2 _ _ _ _ _ _ _ _ _ _ F _ _ G _ _ a b f g x y} u v p pp.
Arguments fmapd_id {A1 A2 B1 B2 _ _ _ _ _ _ _ _ _ _ F _ _ G _ _ a} x.
Arguments fmapd_comp  {A1 A2 B1 B2 _ _ _ _ _ _ _ _ _ _ F _ _ G _ _ a b c f g x y z} u v.

About fmap_id.

Global Instance is1functor_sigma {A1 A2 : Type} (B1 : A1 -> Type) (B2 : A2 -> Type) (F : A1 -> A2) (G : forall a : A1, B1 a -> B2 (F a))
   `{Is1DFunctor A1 A2 B1 B2 F G}  : Is1Functor (functor_sigma F G). 
Proof.
  srapply Build_Is1Functor.
  - intros [a x] [b y] [f u] [g v] [p pp]; cbn in *.
    exact (fmap2 F p ; fmapd2 u v p pp).
  - intros [a x]; cbn.
    exact (fmap_id F a ; fmapd_id x).
  - intros [a x] [b y] [c z] [f u] [g v].
    exact (fmap_comp F f g ; fmapd_comp u v).
Defined.


Section CompositeFunctor.

Context {A1 A2 A3 : Type} {B1 : A1 -> Type} {B2 : A2 -> Type} {B3 : A3 -> Type} `{Is1DCat A1 B1} `{Is1DCat A2 B2} `{Is1DCat A3 B3}
          (F : A1 -> A2) `{!Is0Functor F, !Is1Functor F}
          (G : A2 -> A3) `{!Is0Functor G, !Is1Functor G}
          (FF : forall a:A1, B1 a -> B2 (F a)) (GG : forall a:A2, B2 a -> B3 (G a)) `{!Is0DFunctor B1 B2 F FF, !Is1DFunctor B1 B2 F FF}
          `{!Is0DFunctor B2 B3 G GG, !Is1DFunctor B2 B3 G GG}.

Global Instance is0dfunctor_compose : Is0DFunctor B1 B3 (G o F) (fun (a : A1) (x : B1 a) => ((GG (F a)) o (FF a)) x).
  Proof.
    srapply Build_Is0DFunctor.
    intros a b f x y u.
    exact (fmapd GG (fmapd FF u)).
  Defined.

  Global Instance is1dfunctor_compose : Is1DFunctor B1 B3 (G o F) (fun (a : A1) (x : B1 a) => ((GG (F a)) o (FF a)) x).
  Proof.
    apply Build_Is1DFunctor.
    - intros a b f g x y u v p pp; exact (fmapd2 (fmapd FF u) (fmapd FF v) (fmap2 F p) (fmapd2 u v p pp)).
    - intros a x.
      refine (_ $$@ _).
      + refine (fmapd2 _ _ (fmap_id F a) (fmapd_id x)).
      + apply fmapd_id.
    - intros a b c f g x y z u v.
      refine (_ $$@ _).
      + refine (fmapd2 _ _ (fmap_comp F f g) (fmapd_comp u v)).
      + refine (fmapd_comp _ _).
  Defined.      

End CompositeFunctor.


(** products of displayed (0,1)-categories *)

Global Instance isDgraph_prod {A1 A2 : Type} (B1 : A1 -> Type) (B2 : A2 -> Type) `{IsDGraph A1 B1} `{IsDGraph A2 B2} : @IsDGraph (A1 * A2) (fun x => (B1 (fst x)) * (B2 (snd x))) _.
Proof.
  apply Build_IsDGraph.
  intros [a1 a2] [b1 b2] [f1 f2] [x1 x2] [y1 y2].
  exact ((dHom f1 x1 y1)  * (dHom f2 x2 y2)).
Defined.


Global Instance is01Dcat_prod {A1 A2 : Type} (B1 : A1 -> Type) (B2 : A2 -> Type)  `{Is01DCat A1 B1} `{Is01DCat A2 B2}
  : @Is01DCat (A1 * A2) (is01cat_prod A1 A2) (fun x => (B1 (fst x)) * (B2 (snd x))) _.
Proof.
  srapply Build_Is01DCat; intros [a1 a2] [b1 b2]; cbn.
  - refine ((dId _), (dId _)).
  - intros [c1 c2] [g1 g2] [f1 f2] [x1 x2] [y1 y2] [z1 z2] [v1 v2] [u1 u2].
    exact (dcat_comp v1 u1, dcat_comp v2 u2).
Defined.

Global Instance is0Dgpd_prod {A1 A2 : Type} (B1 : A1 -> Type) (B2 : A2 -> Type) `{Is0DGpd A1 B1} `{Is0DGpd A2 B2}
       : @Is0DGpd (A1 * A2) (fun x => (B1 (fst x)) * (B2 (snd x))) _ _ _ _.
Proof.
  srapply Build_Is0DGpd.
  intros [a1 a2] [b1 b2] [f1 f2] [x1 x2] [y1 y2] [u1 u2]; cbn in *.
  exact (u1^$$, u2^$$).
Defined.

(** comparison functors between product of sigmas and sigma of product *)

Global Instance is0functor_sigma_prod {A1 A2 : Type} (B1 : A1 -> Type) (B2 : A2 -> Type) `{Is01DCat A1 B1} `{Is01DCat A2 B2} : @Is0Functor ((sig B1) * (sig B2)) ({ x : (A1 * A2) & (B1 (fst x)) * (B2 (snd x))}) _ _ (fun x => let (u,v) := x in ((u.1, v.1);(u.2, v.2))).
Proof.
  rapply Build_Is0Functor.
  intros [[a1 x1] [a2 x2]] [[b1 y1] [b2 y2]]; cbn in *.  
  intros [[f1 u1] [f2 u2]].
  exact ((f1, f2) ; (u1, u2)).
Defined.  

Global Instance is0functor_prod_sigma {A1 A2 : Type} (B1 : A1 -> Type) (B2 : A2 -> Type) `{Is01DCat A1 B1} `{Is01DCat A2 B2} : @Is0Functor ({ x : (A1 * A2) & (B1 (fst x)) * (B2 (snd x))})  ((sig B1) * (sig B2)) _ _ (fun x => ((fst (pr1 x); fst (pr2 x)),(snd (pr1 x); snd (pr2 x)))).
Proof.
  rapply Build_Is0Functor.
  intros [[a1 a2] [x1 x2]] [[b1 b2] [y1 y2]]; cbn in *.  
  intros [[f1 f2] [u1 u2]].
  exact ((f1 ; u1) , (f2; u2)).
Defined.



(** products of displayed 1-categories *)

Global Instance is1Dcat_prod {A1 A2 : Type} `{!Is01Cat A1} `{!Is1Cat A1} `{!Is01Cat A2} `{!Is1Cat A2} (B1 : A1 -> Type) (B2 : A2 -> Type)  `{!IsDGraph B1} `{! IsDGraph B2} `{!Is01DCat B1}
      `{!Is01DCat B2} `{!Is1DCat B1} `{!Is1DCat B2}
  : @Is1DCat (A1 * A2) (fun x => (B1 (fst x)) * (B2 (snd x))) (is01cat_prod A1 A2) (isDgraph_prod B1 B2) (is01Dcat_prod B1 B2) (is1cat_prod A1 A2).
Proof.
  srapply (@Build_Is1DCat (A1 * A2)  (fun x => (B1 (fst x)) * (B2 (snd x)))
                         (is01cat_prod A1 A2) (isDgraph_prod B1 B2)
                         (is01Dcat_prod B1 B2) (is1cat_prod A1 A2));
    intros [a1 a2] [b1 b2]; cbn in *.
  - intros [x1 x2] [y1 y2]; refine (isDgraph_prod _ _).
  - intros [x1 x2] [y1 y2]; refine (is01Dcat_prod _ _).
  - intros [x1 x2] [y1 y2]; refine (is0Dgpd_prod _ _).
  - intros [c1 c2] [x1 x2] [y1 y2] [z1 z2] [f1 f2] [g1 g2] [v1 v2]; cbn in *.
    apply Build_Is0DFunctor.
    intros [h1 h2] [k1 k2] [p1 p2] [s1 s2] [t1 t2] [pp1 pp2]; cbn in *.
    exact (dcat_postwhisker v1 pp1, dcat_postwhisker v2 pp2).
  - intros [c1 c2] [x1 x2] [y1 y2] [z1 z2] [f1 f2] [g1 g2] [v1 v2]; cbn in *.
    apply Build_Is0DFunctor.
    intros [h1 h2] [k1 k2] [p1 p2] [s1 s2] [t1 t2] [pp1 pp2]; cbn in *.
    exact (dcat_prewhisker v1 pp1, dcat_prewhisker v2 pp2).
  - intros [c1 c2] [d1 d2] [f1 f2] [g1 g2] [h1 h2] [x1 x2] [y1 y2] [z1 z2] [w1 w2] [u1 u2] [v1 v2] [t1 t2]; cbn in *.
    exact (dcat_assoc u1 v1 t1, dcat_assoc u2 v2 t2).
  - intros [f1 f2] [x1 x2] [y1 y2] [u1 u2].
    exact (dcat_idl u1, dcat_idl u2).
  - intros [f1 f2] [x1 x2] [y1 y2] [u1 u2].
    exact (dcat_idr u1, dcat_idr u2).
Defined.


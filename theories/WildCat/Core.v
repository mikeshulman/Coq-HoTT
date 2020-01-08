(* -*- mode: coq; mode: visual-line -*-  *)

(* Don't import the old WildCat *)
Require Import Basics.Overture.
Require Import Basics.PathGroupoids.
Require Import Basics.Notations.
Require Import Basics.Contractible.
Require Import Basics.Equivalences.

Reserved Infix "$o@" (at level 30).

(** * Wild categories, functors, and transformations *)

(* A 0-coherent 1-category has 1-morphisms and operations on them, but no coherence. *)
Class Is0Coh1Cat (A : Type) :=
{
  Hom : A -> A -> Type where "a $-> b" := (Hom a b);
  Id  : forall (a : A), a $-> a;
  Comp : forall (a b c : A), (b $-> c) -> (a $-> b) -> (a $-> c);
}.

Notation "a $-> b" := (Hom a b).
Arguments Comp {A _ a b c} _ _.
Notation "g $o f" := (Comp g f).

(* A 0-coherent notion of equivalence is simply reversible.  (Without 2-cells, we have no way to express that the reverse is an inverse.) *)
Class Has0CohEquivs (A : Type) `{Is0Coh1Cat A} :=
{
  CatEquiv' : A -> A -> Type where "a $<~> b" := (CatEquiv' a b);
  CatIsEquiv' : forall a b, (a $-> b) -> Type;
  cate_fun' : forall a b, (a $<~> b) -> (a $-> b);
  cate_isequiv' : forall a b (f : a $<~> b), CatIsEquiv' a b (cate_fun' a b f);
  cate_buildequiv' : forall a b (f : a $-> b), CatIsEquiv' a b f -> CatEquiv' a b;
  cate_buildequiv_fun' : forall a b (f : a $-> b) (fe : CatIsEquiv' a b f),
      cate_fun' a b (cate_buildequiv' a b f fe) = f;
  cate_inv' : forall {a b : A} (f : a $-> b) {fe : CatIsEquiv' a b f},
      (b $-> a);
}.

(** Since apparently a field of a record can't be the source of a coercion (Coq complains about the uniform inheritance condition, although as officially stated that condition appears to be satisfied), we redefine all the fields of [Has0CohEquivs]. *)

Definition CatEquiv {A} `{Has0CohEquivs A} (a b : A)
  := @CatEquiv' A _ _ a b.

Notation "a $<~> b" := (CatEquiv a b).
Arguments CatEquiv : simpl never.

Definition cate_fun {A} `{Has0CohEquivs A} {a b : A} (f : a $<~> b)
  : a $-> b
  := @cate_fun' A _ _ a b f.

Coercion cate_fun : CatEquiv >-> Hom.

(* Being an equivalence should be a typeclass, but we have to redefine it.  (Apparently [Existing Class] doesn't work.) *)
Class CatIsEquiv {A} `{Has0CohEquivs A} {a b : A} (f : a $-> b)
  := catisequiv : CatIsEquiv' a b f.

Global Instance cate_isequiv {A} `{Has0CohEquivs A} {a b : A} (f : a $<~> b)
  : CatIsEquiv f
  := cate_isequiv' a b f.

Definition Build_CatEquiv {A} `{Has0CohEquivs A} {a b : A}
           (f : a $-> b) {fe : CatIsEquiv f}
  : a $<~> b
  := cate_buildequiv' a b f fe.

Definition cate_buildequiv_fun {A} `{Has0CohEquivs A} {a b : A}
           (f : a $-> b) {fe : CatIsEquiv f}
  : cate_fun (Build_CatEquiv f) = f
  := cate_buildequiv_fun' a b f fe.

(* A (0-coherent 1-)groupoid is a category whose morphisms are all equivalences. *)
Class IsGroupoid (A : Type) `{Has0CohEquivs A} :=
  { catie_gpd : forall (a b : A) (f : a $-> b), CatIsEquiv f }.
Global Existing Instance catie_gpd.

(* A 0-coherent 1-functor acts on morphisms, but satisfies no axioms. *)
Class Is0Coh1Functor {A B : Type} `{Is0Coh1Cat A} `{Is0Coh1Cat B} (F : A -> B)
  := { fmap : forall (a b : A) (f : a $-> b), F a $-> F b }.

Arguments fmap {_ _ _ _} F {_ _ _} f.

(* Products preserve 0-coherent 1-categories. *)
Global Instance is0coh1cat_prod A B `{Is0Coh1Cat A} `{Is0Coh1Cat B}
  : Is0Coh1Cat (A * B).
Proof.
  refine (Build_Is0Coh1Cat (A * B) (fun x y => (fst x $-> fst y) * (snd x $-> snd y)) _ _).
  - intros [a b]; exact (Id a, Id b).
  - intros [a1 b1] [a2 b2] [a3 b3] [f1 g1] [f2 g2]; cbn in *.
    exact (f1 $o f2 , g1 $o g2).
Defined.

(** To avoid having to define a separate notion of "two-variable functor", we define two-variable functors in uncurried form.  The following definition applies such a two-variable functor, with a currying built in. *)
Definition fmap11 {A B C : Type} `{Is0Coh1Cat A} `{Is0Coh1Cat B} `{Is0Coh1Cat C}
  (F : A -> B -> C) {H2 : Is0Coh1Functor (uncurry F)}
  {a1 a2 : A} {b1 b2 : B} (f1 : a1 $-> a2) (f2 : b1 $-> b2)
  : F a1 b1 $-> F a2 b2
  := @fmap _ _ _ _ (uncurry F) H2 (a1, b1) (a2, b2) (f1, f2).

(* A 0-coherent 2-category has its hom-types enhanced to 0-coherent 1-categories and its composition operations to 0-coherent 1-functors. *)
Class Is0Coh2Cat (A : Type) `{Is0Coh1Cat A} :=
{
  is0coh1cat_hom : forall (a b : A), Is0Coh1Cat (a $-> b) ;
  has0cohequivs_hom : forall (a b : A), Has0CohEquivs (a $-> b) ;
  isgpd_hom : forall (a b : A), IsGroupoid (a $-> b) ;
  is0coh1functor_comp : forall (a b c : A), Is0Coh1Functor (uncurry (@Comp A _ a b c))
}.
Global Existing Instance is0coh1cat_hom.
Global Existing Instance has0cohequivs_hom.
Global Existing Instance isgpd_hom.
Global Existing Instance is0coh1functor_comp.

Definition Comp2 {A} `{Is0Coh2Cat A} {a b c : A}
           {f g : a $-> b} {h k : b $-> c}
           (q : h $-> k) (p : f $-> g)
  : (h $o f $-> k $o g)
  := fmap11 Comp q p.

Infix "$o@" := Comp2.

Definition WhiskerL_Htpy {A} `{Is0Coh2Cat A} {a b c : A}
           {f g : a $-> b} (h : b $-> c) (p : f $-> g)
  : h $o f $-> h $o g
  := (Id h) $o@ p.
Notation "h $@L p" := (WhiskerL_Htpy h p).

Definition WhiskerR_Htpy {A} `{Is0Coh2Cat A} {a b c : A}
           {f g : b $-> c} (p : f $-> g) (h : a $-> b)
  : f $o h $-> g $o h
  := p $o@ (Id h).
Notation "p $@R h" := (WhiskerR_Htpy p h).

Definition GpdHom {A} `{IsGroupoid A} (a b : A) := a $-> b.
Notation "a $== b" := (GpdHom a b).

Definition GpdComp {A} `{IsGroupoid A} {a b c : A}
  : (a $== b) -> (b $== c) -> (a $== c)
  := fun p q => q $o p.
Infix "$@" := GpdComp.

Definition GpdInv {A} `{IsGroupoid A} {a b : A}
  : (a $== b) -> (b $== a)
  := fun p => @cate_inv' _ _ _  a b p (catie_gpd a b p).
Notation "p ^$" := (GpdInv p).

Definition GpdHom_path {A} `{IsGroupoid A} {a b : A} (p : a = b)
  : a $== b.
Proof.
  destruct p; apply Id.
Defined.

(** Generalizing function extensionality, "Morphism extensionality" states that homwise [GpdHom_path] is an equivalence. *)
Class HasMorExt (A : Type) `{Is0Coh2Cat A} :=
  { isequiv_Htpy_path : forall a b f g, IsEquiv (@GpdHom_path (a $-> b) _ _ _ f g) }.
Global Existing Instance isequiv_Htpy_path.

Definition path_Htpy {A} `{HasMorExt A} {a b : A} {f g : a $-> b} (p : f $== g) : f = g
  := GpdHom_path^-1 p.

(* A 1-coherent 1-category satisfies associativity and unit laws up to 2-cells (so it must be at least a 0-coherent 2-category).  We duplicate the reversed associativity and double-identity laws to make more duality operations definitionally involutive. *)
Class Is1Coh1Cat (A : Type) `{Is0Coh2Cat A} := Build_Is1Coh1Cat'
{
  cat_assoc : forall a b c d (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f $== h $o (g $o f);
  cat_assoc_opp : forall a b c d (f : a $-> b) (g : b $-> c) (h : c $-> d),
    h $o (g $o f) $== (h $o g) $o f;
  cat_idl : forall a b (f : a $-> b), Id b $o f $== f;
  cat_idr : forall a b (f : a $-> b), f $o Id a $== f;
  cat_idlr : forall a, Id a $o Id a $== Id a;
}.

(* But in practice we don't want to have to give those extra data. *)
Definition Build_Is1Coh1Cat (A : Type) `{Is0Coh2Cat A}
 (cat_assoc' : forall a b c d (f : a $-> b) (g : b $-> c) (h : c $-> d),
  (h $o g) $o f $== h $o (g $o f))
 (cat_idl' : forall a b (f : a $-> b), Id b $o f $== f)
 (cat_idr' : forall a b (f : a $-> b), f $o Id a $== f)
  : Is1Coh1Cat A
  := Build_Is1Coh1Cat' A _ _ cat_assoc'
      (fun a b c d f g h => (cat_assoc' a b c d f g h)^$)
      cat_idl' cat_idr' (fun a => cat_idl' a a (Id a)).

Arguments cat_assoc {_ _ _ _ _ _ _ _} f g h.
Arguments cat_assoc_opp {_ _ _ _ _ _ _ _} f g h.
Arguments cat_idl {_ _ _ _ _ _} f.
Arguments cat_idr {_ _ _ _ _ _} f.
Arguments cat_idlr {_ _ _ _} a.

(** Often, the coherences are actually equalities rather than homotopies. *)
Class Is1Coh1Cat_Strong (A : Type) `{Is0Coh2Cat A} := Build_Is1Coh1Cat_Strong'
{
  cat_assoc_strong : forall a b c d
    (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f = h $o (g $o f);
  cat_assoc_opp_strong : forall a b c d
    (f : a $-> b) (g : b $-> c) (h : c $-> d),
    h $o (g $o f) = (h $o g) $o f;
  cat_idl_strong : forall a b (f : a $-> b), Id b $o f = f;
  cat_idr_strong : forall a b (f : a $-> b), f $o Id a = f;
  cat_idlr_strong : forall a, Id a $o Id a = Id a;
}.

Definition Build_Is1Coh1Cat_Strong (A : Type) `{Is0Coh2Cat A}
  (cat_assoc' : forall a b c d (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f = h $o (g $o f))
  (cat_idl' : forall a b (f : a $-> b), Id b $o f = f)
  (cat_idr' : forall a b (f : a $-> b), f $o Id a = f)
  : Is1Coh1Cat_Strong A
  := Build_Is1Coh1Cat_Strong' A _ _ cat_assoc'
    (fun a b c d f g h => (cat_assoc' a b c d f g h)^)
    cat_idl' cat_idr' (fun a => cat_idl' a a (Id a)).

Arguments cat_assoc_strong {_ _ _ _ _ _ _ _} f g h.
Arguments cat_assoc_opp_strong {_ _ _ _ _ _ _ _} f g h.
Arguments cat_idl_strong {_ _ _ _ _ _} f.
Arguments cat_idr_strong {_ _ _ _ _ _} f.
Arguments cat_idr_strong {_ _ _ _} a.

Global Instance is1coh1cat_strong A
       {ac0 : Is0Coh1Cat A} {ac2 : Is0Coh2Cat A}
       {ac11 : Is1Coh1Cat_Strong A} : Is1Coh1Cat A.
Proof.
  srapply Build_Is1Coh1Cat'; intros; apply GpdHom_path.
  - serapply cat_assoc_strong.
  - serapply cat_assoc_opp_strong.
  - serapply cat_idl_strong.
  - serapply cat_idr_strong.
  - serapply cat_idlr_strong.
Defined.

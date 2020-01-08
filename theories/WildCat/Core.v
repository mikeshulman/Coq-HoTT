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
  cat_comp : forall (a b c : A), (b $-> c) -> (a $-> b) -> (a $-> c);
}.

Notation "a $-> b" := (Hom a b).
Arguments cat_comp {A _ a b c} _ _.
Notation "g $o f" := (cat_comp g f).

(* A 0-coherent 1-groupoid is a category whose morphisms can be reversed. *)
Class Is0Coh1Gpd (A : Type) `{Is0Coh1Cat A} :=
  { gpd_rev : forall {a b : A}, (a $-> b) -> (b $-> a) }.

Definition GpdHom {A} `{Is0Coh1Gpd A} (a b : A) := a $-> b.
Notation "a $== b" := (GpdHom a b).

Definition gpd_comp {A} `{Is0Coh1Gpd A} {a b c : A}
  : (a $== b) -> (b $== c) -> (a $== c)
  := fun p q => q $o p.
Infix "$@" := gpd_comp.

Notation "p ^$" := (gpd_rev p).

Definition GpdHom_path {A} `{Is0Coh1Gpd A} {a b : A} (p : a = b)
  : a $== b.
Proof.
  destruct p; apply Id.
Defined.

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

(* A 0-coherent (2,1)-category has its hom-types enhanced to 0-coherent 1-groupoids and its composition operations to 0-coherent 1-functors. *)
Class Is0Coh2Cat (A : Type) `{Is0Coh1Cat A} :=
{
  is0coh1cat_hom : forall (a b : A), Is0Coh1Cat (a $-> b) ;
  isgpd_hom : forall (a b : A), Is0Coh1Gpd (a $-> b) ;
  is0coh1functor_comp : forall (a b c : A), Is0Coh1Functor (uncurry (@cat_comp A _ a b c))
}.
Global Existing Instance is0coh1cat_hom.
Global Existing Instance isgpd_hom.
Global Existing Instance is0coh1functor_comp.

Definition Comp2 {A} `{Is0Coh2Cat A} {a b c : A}
           {f g : a $-> b} {h k : b $-> c}
           (q : h $-> k) (p : f $-> g)
  : (h $o f $-> k $o g)
  := fmap11 cat_comp q p.

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

(** Generalizing function extensionality, "Morphism extensionality" states that homwise [GpdHom_path] is an equivalence. *)
Class HasMorExt (A : Type) `{Is0Coh2Cat A} :=
  { isequiv_Htpy_path : forall a b f g, IsEquiv (@GpdHom_path (a $-> b) _ _ f g) }.
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

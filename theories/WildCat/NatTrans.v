Require Import Basics.
Require Import WildCat.Core.
Require Import WildCat.Square.

(** ** Natural transformations *)

Definition Transformation {A B : Type} `{IsGraph B} (F : A -> B) (G : A -> B)
  := forall (a : A), F a $-> G a.

Notation "F $=> G" := (Transformation F G).

(** A 1-natural transformation is natural up to a 2-cell, so its domain must be a 1-category. *)
Class Is1Natural {A B : Type} `{IsGraph A} `{Is1Cat B}
      (F : A -> B) `{!Is0Functor F} (G : A -> B) `{!Is0Functor G}
      (alpha : F $=> G) :=
{
  isnat : forall a a' (f : a $-> a'),
    Square (fmap F f) (fmap G f) (alpha a) (alpha a');
}.

Arguments isnat {_ _ _ _ _ _ _ _ _} alpha {alnat _ _} f : rename.

(** The transposed natural square *)
Definition isnat_tr {A B : Type} `{IsGraph A} `{Is1Cat B}
      {F : A -> B} `{!Is0Functor F} {G : A -> B} `{!Is0Functor G}
      (alpha : F $=> G) `{!Is1Natural F G alpha}
      {a a' : A} (f : a $-> a')
  : Square (alpha a) (alpha a') (fmap F f) (fmap G f)
  := (isnat alpha f)^$.

Definition id_transformation {A B : Type} `{Is01Cat B} (F : A -> B)
  : F $=> F
  := fun a => Id (F a).

Global Instance is1natural_id {A B : Type} `{IsGraph A} `{Is1Cat B}
       (F : A -> B) `{!Is0Functor F}
  : Is1Natural F F (id_transformation F).
Proof.
  apply Build_Is1Natural; intros a b f; cbn. exact vrfl.
Defined.

Definition comp_transformation {A B : Type} `{Is01Cat B}
           {F G K : A -> B} (gamma : G $=> K) (alpha : F $=> G)
  : F $=> K
  := fun a => gamma a $o alpha a.

Global Instance is1natural_comp {A B : Type} `{IsGraph A} `{Is1Cat B}
       {F G K : A -> B} `{!Is0Functor F} `{!Is0Functor G} `{!Is0Functor K}
       (gamma : G $=> K) `{!Is1Natural G K gamma}
       (alpha : F $=> G) `{!Is1Natural F G alpha}
  : Is1Natural F K (comp_transformation gamma alpha).
Proof.
  apply Build_Is1Natural; intros a b f; cbn.
  exact (isnat alpha f $@v isnat gamma f).
Defined.

(** Modifying a transformation to something pointwise equal preserves naturality. *)
Definition is1natural_homotopic {A B : Type} `{Is01Cat A} `{Is1Cat B}
      {F : A -> B} `{!Is0Functor F} {G : A -> B} `{!Is0Functor G}
      {alpha : F $=> G} (gamma : F $=> G) `{!Is1Natural F G gamma}
      (p : forall a, alpha a $== gamma a)
  : Is1Natural F G alpha.
Proof.
  constructor; intros a b f.
  refine (_ $@hL _ $@hR p b).
  1: exact (p a). 
  exact (isnat gamma f).
Defined.

Definition cat_assoc_transformation {A : Type} `{Is1Cat A} {a b c d : A}
  : (cat_comp_lassoc a b c d) $=> (cat_comp_rassoc a b c d).
Proof.
  intros [[f g] h] ; exact (cat_assoc f g h).
Defined.

Definition cat_idl_transformation {A : Type} `{Is1Cat A} {a b : A}
  : cat_comp_idl a b $=> idmap.
Proof.
  intro f ; exact (cat_idl f).
Defined.


Definition cat_idr_transformation {A : Type} `{Is1Cat A} {a b : A}
  : cat_comp_idr a b $=> idmap.
Proof.
  intro f ; exact (cat_idr f).
Defined.

Class Is21Cat (A : Type) `{Is1Cat A} :=
{
  is1cat_hom : forall (a b : A), Is1Cat (a $-> b) ;
  is1gpd_hom : forall (a b : A), Is1Gpd (a $-> b) ;
  is1functor_comp : forall (a b c : A),
      Is1Functor (uncurry (@cat_comp A _ a b c)) ;

  (** *** Associator *)
  is1natural_cat_assoc : forall (a b c d : A),
      Is1Natural (cat_comp_lassoc a b c d) (cat_comp_rassoc a b c d)
                 cat_assoc_transformation ;

  (** *** Unitors *)
  is1natural_cat_idl : forall (a b : A),
      Is1Natural (cat_comp_idl a b) idmap
                 cat_idl_transformation;

  is1natural_cat_idr : forall (a b : A),
      Is1Natural (cat_comp_idr a b) idmap
                 cat_idr_transformation;

  (** *** Coherence *)
  cat_pentagon : forall (a b c d e : A)
                        (f : a $-> b) (g : b $-> c) (h : c $-> d) (k : d $-> e),
      (k $@L cat_assoc f g h) $o (cat_assoc f (h $o g) k) $o (cat_assoc g h k $@R f)
      $== (cat_assoc (g $o f) h k) $o (cat_assoc f g (k $o h)) ;

  cat_tril : forall (a b c : A) (f : a $-> b) (g : b $-> c),
      (g $@L cat_idl f) $o (cat_assoc f (Id b) g) $== (cat_idr g $@R f)
}.

Global Existing Instance is1cat_hom.
Global Existing Instance is1gpd_hom.
Global Existing Instance is1functor_comp.
Global Existing Instance is1natural_cat_assoc.
Global Existing Instance is1natural_cat_idl.
Global Existing Instance is1natural_cat_idr.
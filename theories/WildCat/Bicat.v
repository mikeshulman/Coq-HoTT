(* -*- mode: coq; mode: visual-line -*-  *)

Require Export Basics.
Require Export WildCat.Core.
Require Export WildCat.Equiv.
Require Export WildCat.Prod.

(** * 2-coherent 2-wild categories *)

Class Is2Coh2Cat_Pre (A : Type) `{Is0Coh1Cat A} :=
{
  is0coh1cat_hom : forall (a b : A), Is0Coh1Cat (a $-> b) ;
  is0coh21cat_hom : forall (a b : A), Is0Coh21Cat (a $-> b) ;
  is1coh1cat_hom : forall (a b : A), Is1Coh1Cat (a $-> b) ;
  hasequivs_hom : forall (a b : A), HasEquivs (a $-> b) ;

  is0coh1functor_comp : forall (a b c : A),
      Is0Coh1Functor (uncurry (@cat_comp A _ a b c)) ;

  is1coh1functor_comp : forall (a b c : A),
      Is1Coh1Functor (uncurry (@cat_comp A _ a b c))
}.

Existing Instance is0coh1cat_hom.
Existing Instance is0coh21cat_hom.
Existing Instance is1coh1cat_hom.
Existing Instance hasequivs_hom.
Existing Instance is0coh1functor_comp.
Existing Instance is1coh1functor_comp.

Definition is0coh1cat_2coh2cat_pre {A : Type} `{Is2Coh2Cat_Pre A}
  : Is0Coh1Cat A.
Proof.
  srapply Build_Is0Coh1Cat.
  - intros a b ; exact (core (a $-> b)).
  - intro a ; apply Id.
  - intros a b c ; apply cat_comp.
Defined.

(* Typeclasses eauto := debug. *)

Definition is0coh21cat_2coh2cat_pre {A : Type} `{Is2Coh2Cat_Pre A}
  : @Is0Coh21Cat A is0coh1cat_2coh2cat_pre.
Proof.
  simple notypeclasses refine (Build_Is0Coh21Cat _ _ _ _ _).
  - intros a b ; apply is0coh1cat_core.
  - intros a b ; apply is0coh1gpd_core.
  - intros a b c.
    rapply Build_Is0Coh1Functor.
    intros [f g] [f' g'] [al be].
    cbn. cbn in *. cbv in f, g, f', g'.
    exact (@fmap11 _ _ _ _ _ _ cat_comp is0coh1functor_comp f g f' g'
                   al be).
Defined.


Class Is2Coh2Cat_Pre1 (A : Type) `{Is2Coh2Cat_Pre A} :=
{
  is0coh1functor_comp : forall (a b c : A),
      Is0Coh1Functor
        (uncurry (@cat_comp A is0coh1cat_2coh2cat_pre a b c)) ;

  is1coh1functor_comp : forall (a b c : A),
      Is1Coh1Functor
        (uncurry (@cat_comp A is0coh1cat_2coh2cat_pre a b c))
}.




Set Printing Implicit.


(*
Definition bicat_comp_lassoc {A : Type} `{Is1Coh1Cat A} (a b c d : A)
  : (a $-> b) * (b $-> c) * (c $-> d) -> a $-> d.
Proof.
  intros [[f g] h].
  exact ((h $o g) $o f).
Defined.

Definition bicat_comp_rassoc {A : Type} `{Is1Coh1Cat A} (a b c d : A)
  : (a $-> b) * (b $-> c) * (c $-> d) -> a $-> d.
Proof.
  intros [[f g] h].
  exact (h $o (g $o f)).
Defined.

Global Instance is0coh1cat_bicat_assoc_dom {A : Type} `{Is1Coh1Cat A}
       {a b c d : A} : Is0Coh1Cat ((a $-> b) * (b $-> c) * (c $-> d)).
Proof.
  rapply is0coh1cat_prod.
Defined.

Global Instance is0coh1functor_bicat_comp_lassoc
       {A : Type} `{Is1Coh1Cat A}
       {a b c d : A} : Is0Coh1Functor (bicat_comp_lassoc a b c d).
Proof.
  apply Build_Is0Coh1Functor.
  intros [[f g] h] [[f' g'] h'] [[al be] ga] ;
    exact (fmap11 cat_comp (fmap11 cat_comp ga be) al).
Defined.

Global Instance is0coh1functor_bicat_comp_rassoc
       {A : Type} `{Is1Coh1Cat A}
       {a b c d : A} : Is0Coh1Functor (bicat_comp_rassoc a b c d).
Proof.
  apply Build_Is0Coh1Functor.
  intros [[f g] h] [[f' g'] h'] [[al be] ga] ;
    exact (fmap11 cat_comp ga (fmap11 cat_comp be al)).
Defined.

Definition cat_assoc_nat {A : Type} `{Is1Coh1Cat A} {a b c d : A}
  : (bicat_comp_lassoc a b c d) $=> (bicat_comp_rassoc a b c d).
Proof.
  intros [[f g] h] ; exact (cat_assoc f g h).
Defined.

Definition cat_idl_nat {A : Type} `{Is1Coh1Cat A} {a b : A}
  : (fun (f : a $-> b) => Id b $o f) $=> idmap.
Proof.
  intro f ; exact (cat_idl f).
Defined.

Definition cat_idr_nat {A : Type} `{Is1Coh1Cat A} {a b : A}
  : (fun (f : a $-> b) => f $o Id a) $=> idmap.
Proof.
  intro f ; exact (cat_idr f).
Defined.
*)

(** Notably absent due to groupoidal assumptions:

  We might additionally have asked for such data, but these are
  locally groupoidal, see [Is0Cho2Cat.isgpd_hom],


  bicat_assoc_catie : forall (a b c d : A) (f : a $-> b)
                             (g : b $-> c) (h : c $-> d),
                             CatIsEquiv (bicat_assoc a b c d f g h);
 *)

Class Is2Coh2Cat (A : Type) `{Is1Coh1Cat A} := Build_Is2Coh2Cat'
{
  is0coh1cat_hom : forall (a b : A), Is0Coh1Cat (a $-> b) ;
  is0coh2cat_hom : forall (a b : A), Is0Coh2Cat (a $-> b) ;
  is1coh1cat_hom : forall (a b : A), Is1Coh1Cat (a $-> b) ;
  hasequivs_hom : forall (a b : A), HasEquivs (a $-> b) ;

  is1coh1functor_comp : forall (a b c : A),
      Is1Coh1Functor (uncurry (@cat_comp A _ a b c)) ;

  (** *** Associator *)
  is1natural_cat_assoc : forall (a b c d : A),
      Is1Natural (bicat_comp_lassoc a b c d)
                 (bicat_comp_rassoc a b c d)
                 cat_assoc_nat ;

  (** *** Unitors *)
  is1natural_cat_idl : forall (a b : A),
      Is1Natural (fun (f : a $-> b) => Id b $o f)
                 idmap
                 cat_idl_nat;

  is1natural_cat_idr : forall (a b : A),
      Is1Natural _ idmap (@cat_idr_nat _ _ _ _ a b) ;

  (** *** Coherence *)
  bicat_pentagon : forall (a b c d e : A)
                     (f : a $-> b) (g : b $-> c)
                     (h : c $-> d) (k : d $-> e),
      (Id k $o@ cat_assoc_nat (f,g,h))
        $o cat_assoc_nat (f,(h $o g),k)
        $o (cat_assoc_nat (g,h,k) $o@ Id f)
      $== cat_assoc_nat ((g $o f),h,k)
          $o cat_assoc_nat (f,g,(k $o h)) ;

  bicat_tril : forall (a b c : A) (f : a $-> b) (g : b $-> c),
      Id g $o@ cat_idl_nat f $o cat_assoc_nat  (f,(Id b),g)
         $== cat_idr_nat g $o@ Id f
}.

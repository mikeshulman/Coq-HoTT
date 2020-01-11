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

  is0coh21functor_comp : forall (a b c : A),
      Is0Coh21Functor (uncurry (@cat_comp A _ a b c)) ;

  is1coh1functor_comp : forall (a b c : A),
      Is1Coh1Functor (uncurry (@cat_comp A _ a b c))
}.

Existing Instance is0coh1cat_hom.
Existing Instance is0coh21cat_hom.
Existing Instance is1coh1cat_hom.
Existing Instance hasequivs_hom.
Existing Instance is0coh1functor_comp.
Existing Instance is0coh21functor_comp.
Existing Instance is1coh1functor_comp.

Definition coh_comp {A : Type} `{Is2Coh2Cat_Pre A} {a b c : A}
  : core (b $-> c) -> core (a $-> b) -> core (a $-> c).
Proof.
  intros [f] [g] ; apply Build_core ; exact (f $o g).
Defined.

Definition coh_id {A : Type} `{Is2Coh2Cat_Pre A} (a : A)
  : core (a $-> a).
Proof.
  apply Build_core, Id.
Defined.

Definition is0coh1cat_2coh2cat_pre {A : Type} `{Is2Coh2Cat_Pre A}
  : Is0Coh1Cat A.
Proof.
  simple refine (Build_Is0Coh1Cat _ _ _ _).
  - intros a b ; exact (core (a $-> b)).
  - intro a ; apply coh_id.
  - intros a b c ; apply coh_comp.
Defined.

Global Instance is0coh1functor_bicat_comp {A : Type}
       `{Is2Coh2Cat_Pre A} {a b c : A}
  : Is0Coh1Functor (uncurry
                      (@cat_comp _  is0coh1cat_2coh2cat_pre a b c)).
Proof.
  rapply Build_Is0Coh1Functor.
  intros [[f] [g]] [[f'] [g']] [al be].
  exact (emap11 cat_comp al be).
Defined.

Global Instance is0coh21cat_2coh2cat_pre {A : Type} `{Is2Coh2Cat_Pre A}
  : @Is0Coh21Cat A is0coh1cat_2coh2cat_pre.
Proof.
  rapply (Build_Is0Coh21Cat A is0coh1cat_2coh2cat_pre).
Defined.

Definition bicat_comp_lassoc {A : Type} `{Is2Coh2Cat_Pre A}
           (a b c d : A) : core (a $-> b) * core (b $-> c) *
                           core (c $-> d) -> core (a $-> d).
Proof.
  intros [[[f] [g]] [h]] ; apply Build_core ; exact ((h $o g) $o f).
Defined.

Definition bicat_comp_rassoc {A : Type} `{Is2Coh2Cat_Pre A}
           (a b c d : A) : core (a $-> b) * core (b $-> c) *
                           core (c $-> d) -> core (a $-> d).
Proof.
  intros [[[f] [g]] [h]] ; apply Build_core ; exact (h $o (g $o f)).
Defined.

Global Instance is0coh1cat_bicat_assoc_dom {A : Type}
       `{Is2Coh2Cat_Pre A} {a b c d : A}
  : Is0Coh1Cat (core (a $-> b) * core (b $-> c) * core (c $-> d)).
Proof.
  rapply is0coh1cat_prod.
Defined.

(* I'm not sure why i have to do this, but $o@ just stalls, and in
fact even $o fails. *)

Infix "$oC" := coh_comp (at level 30).

Definition coh_comp2 {A : Type} `{Is2Coh2Cat_Pre A}
           {a b c : A} {f g : core (a $-> b)} {h k : core (b $-> c)}
           (al : h $-> k) (be : f $-> g)
  : h $oC f $-> k $oC g := fmap11 coh_comp al be.

Infix "$o@C" := coh_comp2 (at level 30).

Global Instance is0coh1functor_bicat_comp_lassoc
       {A : Type} `{Is2Coh2Cat_Pre A}
       {pf : @Is1Coh1Cat A is0coh1cat_2coh2cat_pre _ }
       {a b c d : A} : Is0Coh1Functor (bicat_comp_lassoc a b c d).
Proof.
  apply Build_Is0Coh1Functor.
  intros [[f g] h] [[f' g'] h'] [[al be] ga].
  exact (ga $o@C be $o@C al).
Defined.

Global Instance is0coh1functor_bicat_comp_rassoc
       {A : Type} `{Is2Coh2Cat_Pre A}
       {pf : @Is1Coh1Cat A is0coh1cat_2coh2cat_pre _}
       {a b c d : A} : Is0Coh1Functor (bicat_comp_rassoc a b c d).
Proof.
  apply Build_Is0Coh1Functor.
  intros [[f g] h] [[f' g'] h'] [[al be] ga].
  exact (ga $o@C (be $o@C al)).
Defined.

Definition bicat_assoc_nat {A : Type} `{Is2Coh2Cat_Pre A}
           {pf : @Is1Coh1Cat A is0coh1cat_2coh2cat_pre _}
           {a b c d : A}
  : (bicat_comp_lassoc a b c d) $=> (bicat_comp_rassoc a b c d).
Proof.
  intros [[f g] h] ; rapply (@cat_assoc A _ _ pf).
Defined.

Definition bicat_idl_fun {A : Type} `{Is2Coh2Cat_Pre A}
           (a b : A) (f : core (a $-> b)) : core (a $-> b)
  := (coh_id b) $oC f.

Definition bicat_idr_fun {A : Type} `{Is2Coh2Cat_Pre A}
           (a b : A) (f : core (a $-> b)) : core (a $-> b)
  := f $oC (coh_id a).

Global Instance is0coh1functor_bicat_idl_fun {A : Type}
       `{Is2Coh2Cat_Pre A} {a b : A}
  : Is0Coh1Functor (bicat_idl_fun a b).
Proof.
  rapply Build_Is0Coh1Functor.
  intros f g al.
  exact (Id (coh_id b) $o@C al).
Defined.

Global Instance is0coh1functor_bicat_idr_fun {A : Type}
       `{Is2Coh2Cat_Pre A} {a b : A}
  : Is0Coh1Functor (bicat_idr_fun a b).
Proof.
  rapply Build_Is0Coh1Functor.
  intros f g al.
  exact (al $o@C Id (coh_id a)).
Defined.

Definition bicat_idl_nat {A : Type} `{Is2Coh2Cat_Pre A}
           {pf : @Is1Coh1Cat A is0coh1cat_2coh2cat_pre _}
           {a b : A}
  : bicat_idl_fun a b $=> idmap.
Proof.
  intro f ; rapply (@cat_idl _ _ _ pf).
Defined.

Definition bicat_idr_nat {A : Type}
           `{Is2Coh2Cat_Pre A}
           {pf : @Is1Coh1Cat A is0coh1cat_2coh2cat_pre _}
           {a b : A}
  : bicat_idr_fun a b $=> idmap.
Proof.
  intro f ; rapply (@cat_idr _ _ _ pf).
Defined.

Class Is2Coh2Cat (A : Type) `{Is2Coh2Cat_Pre A} :=
{
  is1coh1cat_core : @Is1Coh1Cat A is0coh1cat_2coh2cat_pre
                                is0coh21cat_2coh2cat_pre ;
  (** *** Associator *)
  is1natural_cat_assoc : forall (a b c d : A),
      Is1Natural (bicat_comp_lassoc a b c d)
                 (bicat_comp_rassoc a b c d)
                 bicat_assoc_nat ;

  (** *** Unitors *)
  is1natural_cat_idl : forall (a b : A),
      Is1Natural (bicat_idl_fun a b) idmap bicat_idl_nat;


  is1natural_cat_idr : forall (a b : A),
      Is1Natural (bicat_idr_fun a b) idmap bicat_idr_nat;

  (** *** Coherence *)
  bicat_tri : forall (a b c : A) (f : core (a $-> b)) (g : core (b $-> c)),
      Id g $o@C bicat_idl_nat f $o bicat_assoc_nat (f,(coh_id b),g)
         $== bicat_idr_nat g $o@C Id f ;

  bicat_pentagon : forall (a b c d e : A)
                     (f : core (a $-> b)) (g : core (b $-> c))
                     (h : core (c $-> d)) (k : core (d $-> e)),
      (Id k $o@C bicat_assoc_nat (f,g,h))
        $o bicat_assoc_nat (f,(h $oC g),k)
        $o (bicat_assoc_nat (g,h,k) $o@C Id f)
      $== bicat_assoc_nat ((g $oC f),h,k)
          $o bicat_assoc_nat (f,g,(k $oC h)) ;
}.

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


(** Notably absent due to groupoidal assumptions:

  We might additionally have asked for such data, but these are
  locally groupoidal, see [Is0Cho2Cat.isgpd_hom],


  bicat_assoc_catie : forall (a b c d : A) (f : a $-> b)
                             (g : b $-> c) (h : c $-> d),
                             CatIsEquiv (bicat_assoc a b c d f g h);
 *)

Class Is2Coh2Cat (A : Type) `{Is1Coh1Cat A} := Build_Is2Coh2Cat'
{
  is0coh2cat_hom : forall (a b : A), Is0Coh2Cat (a $-> b) ;
  is1coh1cat_hom : forall (a b : A), Is1Coh1Cat (a $-> b) ;

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
*)

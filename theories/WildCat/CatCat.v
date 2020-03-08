(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.Overture.
Require Import Basics.PathGroupoids.
Require Import Basics.Notations.
Require Import Basics.Contractible.
Require Import Basics.Equivalences.
Require Import WildCat.Core.
Require Import WildCat.FunctorCat.
Require Import WildCat.NatTrans.
Require Import WildCat.Equiv.
Require Import WildCat.Induced.
Require Import WildCat.Square. 

(** * Wild categories of wild categories *)

(** ** The wild category of wild (0,1)-categories *)

(** The category of wild graphs is even simpler than the category of wild (0,1)-categories. *)

Record WildGraph :=
  {
    graph_carrier : Type;
    graph_isgraph : IsGraph graph_carrier;
  }.

Coercion graph_carrier : WildGraph >-> Sortclass.

Global Existing Instance graph_isgraph.

Global Instance isgraph_wildgraph : IsGraph WildGraph.
Proof.
  apply Build_IsGraph.
  intros A B.
  exact (Fun01 A B).
Defined.

(** The category of wild (0,1)-categories is simplest, but minimally coherent. *)
Record WildCat01 :=
{
  cat01_carrier : Type;
  cat01_isgraph : IsGraph cat01_carrier;
  cat01_is01cat : Is01Cat cat01_carrier;
}.

(* note for morgan: this allows us to consider WildCats as types. *)
Coercion cat01_carrier : WildCat01 >-> Sortclass.

Global Existing Instance cat01_isgraph.
Global Existing Instance cat01_is01cat.

Global Instance isgraph_wildcat01 : IsGraph WildCat01.
Proof.
  econstructor.
  intros A B.
  exact (Fun01 A B).
Defined.

Global Instance is01cat_wildcat01 : Is01Cat WildCat01.
Proof.
  srapply Build_Is01Cat.
  + intros C. cbn in *.
    exists idmap; exact _.
  + intros A B C [G g] [F f].
    exists (G o F); exact _.
Defined.

(** In fact [WildCat01] is probably a (wild) 1-category and even a (1,2)-category, but we haven't shown that or even defined the latter. *)


(** ** The wild category of wild 1-groupoids *)

Record WildGpd :=
{
  gpd_carrier : Type;
  gpd_isgraph : IsGraph gpd_carrier;
  gpd_is01cat : Is01Cat gpd_carrier;
  gpd_is0gpd : Is0Gpd gpd_carrier;
}.

Coercion gpd_carrier : WildGpd >-> Sortclass.

Global Existing Instance gpd_isgraph.
Global Existing Instance gpd_is01cat.
Global Existing Instance gpd_is0gpd.

Global Instance isgraph_wildgpd : IsGraph WildGpd.
Proof.
  apply Build_IsGraph.
  intros A B.
  exact (Fun01 A B).
Defined.

Global Instance is01cat_wildgpd : Is01Cat WildGpd.
Proof.
  srapply Build_Is01Cat.
  - intros A. cbn in *.
    exists idmap; exact _.
  - intros A B C [G g] [F f].
    exists (G o F); exact _.
Defined.

(** ** The wild category of wild 1-categories *)

(** This should form a wild 2-category. *) 

Record WildCat :=
{
  cat_carrier : Type;
  cat_isgraph : IsGraph cat_carrier;
  cat_is01cat : Is01Cat cat_carrier;
  cat_is1cat : Is1Cat cat_carrier
}.

(* note for morgan: this allows us to consider WildCats as types. *)
Coercion cat_carrier : WildCat >-> Sortclass. 

Global Existing Instance cat_isgraph.
Global Existing Instance cat_is01cat.
Global Existing Instance cat_is1cat.

(** The proofs below are almost identical to those showing that WildCat01 is a (0,1)-category, but we use [Fun11] instead of [Fun01]. *)
Global Instance isgraph_wildcat : IsGraph WildCat.
Proof.
  econstructor.
  intros A B.
  exact (Fun11 A B). (* I'd like to put (core Fun11 A B) here but it breaks the next proof.*)
Defined.

Global Instance is01cat_wildcat : Is01Cat WildCat.
Proof.
  srapply Build_Is01Cat.
  + intro A; rapply (Build_Fun11 _ _ idmap).
  + intros C D E [F ?] [G ?]; cbn in *.
    srapply (Build_Fun11 _ _ (F o G)).
Defined.

(** Now we show WildCat is a 2-category, with a 1-category structure on Fun11 given by natural transformations.  *)

(* But recall the hom-categories in a 1-category need to be a groupoid so we take the hom type between F G : Fun11 to by the type of NatEquiv rather than NatTrans. This however requires the 1-categories to have equivs, so below there is a new record WildCate which records this data. To see this, comment out the first part of the proof below.*)

Global Instance is1cat_wildcat : Is1Cat WildCat.
Proof.
(* new attempted proof with NatEquiv fails for lack of HasEquivs B  
  srapply Build_Is1Cat.
  - intros [A ?] [B ?].
    apply Build_IsGraph; cbn.
    intros [F ?] [G ?].
    refine (NatEquiv F G).
    + 
      apply Build_HasEquiv.
    apply isgraph_fun11.
  - intros A B.
    apply is01cat_fun11.
  - intros A B; cbn.
    apply Build_Is0Gpd.
    intros F G; cbn in *.
    intro alpha; unfold NatTrans.
*)    
(* previously commented out proof
  + intros A B C D f g h.
  exact (Fun1 A B).
  + intros C. cbn in *.
  unfold Fun1. 
  exists (idmap). srapply Build_Is0Coh1Functor. intros a b. cbn.
  exact (idmap).
  + intros A B C; cbn in *; unfold Fun1.
  intros [G g] [F f]. 
  exists ( G o F). 
  srapply Build_Is0Coh1Functor.
  intros u v h. cbn in *.  exact (fmap G ( fmap F h)).
  Defined. *)
Admitted. 

(*
Record WildCate :=
{
  cate_carrier : Type;
  cate_isgraph : IsGraph cate_carrier;
  cate_is01cat : Is01Cat cate_carrier;
  cate_is1cat : Is1Cat cate_carrier;
  cate_hasequivs : HasEquivs cate_carrier;
}.

Coercion cate_carrier : WildCate >-> Sortclass. 

Global Existing Instance cate_isgraph.
Global Existing Instance cate_is01cat.
Global Existing Instance cate_is1cat.
Global Existing Instance cate_hasequivs.

Global Instance isgraph_wildcate : IsGraph WildCate.
Proof.
  econstructor.
  intros A B.
  exact (Fun11 A B).
Defined.

Global Instance is01cat_wildcate : Is01Cat WildCate.
Proof.
  srapply Build_Is01Cat.
  + intro A; rapply (Build_Fun11 _ _ idmap).
  + intros C D E [F ? ?] [G ? ?]; cbn in *.
    srapply (Build_Fun11 _ _ (F o G)).
Defined.

Global Instance is1cat_wildcate : Is1Cat WildCate.
Proof.
  srapply Build_Is1Cat.
  - intros [A ?] [B ?].
    apply Build_IsGraph; cbn.
    intros [F ?] [G ?].
    exact (NatEquiv F G).
  - intros [A ?] [B ?].
    apply Build_Is01Cat; cbn.
    + intros [F ?].
      unfold NatEquiv.
      Locate CatEquiv.
      exists (id_transformation F).
      exists (fun a => id_cate (F a)).
      apply Build_Is1Natural.
      intros a b f; cbn.
      exact (vrefl (fmap F f)).
           
*)

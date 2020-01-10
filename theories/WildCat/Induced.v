(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Import WildCat.Core.
Require Import WildCat.Equiv.


(** showing that a map A -> B of types where B is structured (e.g. some type of category) induces the same level of structure on A, via taking everything to be defined on the image.

This section needs to be separate from core because of HasEquivs usage. *)

(** Mapping to a category induces a category structure on the source. *)

Section Induced_category.
Context {A B : Type} 
  (f : A -> B).
  
Local Instance induced_0coh1cat `{Is0Coh1Cat B}: Is0Coh1Cat A.
Proof.
  serapply Build_Is0Coh1Cat.
  + intros a1 a2. 
  exact (f a1 $-> f a2).
  + intro a. cbn in *. 
  exact (Id (f a)).
  + intros a b c; cbn in *; intros g1 g2.
  exact ( g1 $o g2).
 Defined.
(** Want that the structure map along which we induce the category structure becomes a functor wrt the induced structure *) 
Local Instance inducingmap_is0coh1functor `{Is0Coh1Cat B} : Is0Coh1Functor f.
Proof.
  serapply Build_Is0Coh1Functor.
  intros a b. cbn in *. exact idmap.
  Defined.
Local Instance induced_0coh21cat `{Is0Coh21Cat B} : Is0Coh21Cat A.
Proof.
  serapply Build_Is0Coh21Cat.
  + intros a b. cbn in *. exact _.
  + intros a b. cbn in *. exact _.
  + intros a b c. cbn in *. 
  unfold uncurry. exact _.
Defined.
Local Instance inducingmap_is0coh21functor `{Is0Coh21Cat B} : Is0Coh2Functor f.
Proof. 
  serapply Build_Is0Coh2Functor.
  intros a b g h. cbn in *. exact idmap.
  Defined.
Local Instance induced_1coh1cat `{Is1Coh1Cat B} : Is1Coh1Cat A.
Proof.
  serapply Build_Is1Coh1Cat.
  + intros a b c d; cbn in *. 
  intros u v w. apply cat_assoc.
  + intros a b; cbn in *.
  intros u. apply cat_idl.
  + intros a b; cbn in *.
  intros u. apply cat_idr.
Defined.
Local Instance inducingmap_is1coh1functor `{Is1Coh1Cat B} : Is1Coh1Functor f.
Proof.
  serapply Build_Is1Coh1Functor.
  + intros a. cbn in *. exact (Id _).
  + intros a b c g h. cbn in *. exact (Id _). 
Defined.
End Induced_category.

  (** Stuff about induced HasEquivs.*)
  
Definition induced_hasequivs (A B: Type)(F: A -> B)`{Is1Coh1Cat B}`{!HasEquivs B} : @HasEquivs A _ (induced_0coh21cat F).
Proof.
  serapply Build_HasEquivs.
  + intros a b. exact (F a $<~> F b).
  + intros a b h. apply (CatIsEquiv' (F a) (F b)).
  exact (@fmap _ _ _ _ F (inducingmap_is0coh1functor F) a b h ).
  + intros a b; cbn in *. 
  intros g. exact( cate_fun g).
  + intros a b h; cbn in *. 
  exact (cate_isequiv' _ _ h ).
  + intros a b h; cbn in *. 
  exact ( cate_buildequiv' _ _ h).
  + intros a b h fe; cbn in *. 
  exact ( cate_buildequiv_fun' (F a) (F b) h fe) .
  + intros a b h fe; cbn in *.
  exact(cate_inv'  _ _ h fe ).
  + intros a b h fe; cbn in *.
  exact (cate_issect' _ _ h fe ).
  + intros a b h fe; cbn in *.
   exact (cate_isretr' _ _ _ _ ).
  + intros a b h g m n; cbn in *.  
  exact ( catie_adjointify' _ _ h g m n  ).
  Defined.
 

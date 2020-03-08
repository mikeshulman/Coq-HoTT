(* -*- mode: coq; mode: visual-line -*-  *)
Require Import Basics.
Require Import Types.
Require Import WildCat.Core.
Require Import WildCat.Equiv.
Require Import WildCat.Opposite.
Require Import WildCat.Prod.
Require Import WildCat.Displayed.
Require Import WildCat.CatCat.
Require Import WildCat.FunctorCat.

(** * Grothendieck construction for wild categories *)

(** A sufficiently coherent functor A -> WildCat should induce by covariant Grothendieck construction a displayed category over A. *)

Global Instance isdgraph_grothendieck_graph {A : Type} `{IsGraph A} (B : A -> WildGraph) `{! Is0Functor B} : IsDGraph B.
Proof.
  apply Build_IsDGraph.
  intros a b f x y.
  exact (@Hom (B b) _ (fmap B f x) y).
Defined.

(** There's some obvious redundancy in the next result. The wild 01-category structure on the codomain is not used in any way. But perhaps it's helpful to have a separate lemma? *)

Global Instance isdgraph_grothendieck_01cat {A : Type} `{IsGraph A} (B : A -> WildCat01) `{! Is0Functor B} : IsDGraph B.
Proof.
  apply Build_IsDGraph.
  intros a b f x y.
  exact (@Hom (B b) _ (fmap B f x) y).
Defined.

(* Note a 0-functor B : A -> WildCat01 indexed on a 01-category A isn't sufficient to give a 01-displayed category since, for instance, we would have to produce, given x : B a, an identity arrow in fmap B (Id a) x $-> x, with no coherence that relates fmap B (Id a) x to x. To play around with this uncomment out the following:

Global Instance is01dcat {A : Type} `{Is1Cat A} (B : A -> WildCat01) `{! Is0Functor B} 
 : Is01DCat B.
Proof.
  apply Build_Is01DCat.
  - intros a x; cbn in *.

 *)

Global Instance is0dgpd_grothendieck_gpd {A : Type} `{IsGraph A} (B : A -> WildGpd) `{! Is0Functor B} : IsDGraph B.
Proof.
  apply Build_IsDGraph.
  intros a b f x y.
  exact (@Hom (B b) _ (fmap B f x) y).
Defined.


  
(** TODO: A sufficiently coherent functor A^op -> WildCat should induce by contravariant Grothendieck construction a displayed category over A. *)




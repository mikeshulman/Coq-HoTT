Require Import Basics.
Require Import WildCat.Core.
Require Import WildCat.Prod.
Require Import WildCat.TwoOneCat.
Require Import WildCat.Square.
Require Import WildCat.Displayed.

Section Comma.

  Context {A B C : Type}
    (F : A -> C) (G : B -> C)
    `{Is1Cat A, Is1Cat B, Is21Cat C}
    `{!Is0Functor F, !Is0Functor G,
      !Is1Functor F, !Is1Functor G}.

  Definition DComma : A * B -> Type
    := fun x => F (fst x) $-> G (snd x).

  Global Instance isdgraph_dcomma : IsDGraph DComma.
  Proof.
    srapply Build_IsDGraph.
    intros [a1 b1] [a2 b2] [f g] h i.
    exact (Square h i (fmap F f) (fmap G g)).
  Defined.

  Global Instance is01dcat_dcomma : Is01DCat DComma.
  Proof.
    snrapply Build_Is01DCat.
    + intros [a1 b1] h.
      simpl.
      rapply vconcatL.
      1: rapply fmap_id.
      rapply vconcatR.
      2: rapply fmap_id.
      apply hrefl.
    + intros [a1 b1] [a2 b2] [a3 b3] [f1 g1] [f2 g2].
      intros i j k s t.
      simpl in *.
      rapply vconcatL.
      1: rapply fmap_comp.
      rapply vconcatR.
      2: rapply fmap_comp.
      apply (hconcat t s).
  Defined.

  Global Instance isdgraph_dhom_dcomma a b (x : DComma a) (y : DComma b)
    : IsDGraph (fun f : a $-> b => dHom f x y).
  Proof.
    snrapply Build_IsDGraph.
    intros f g [h1 h2] p q.
    simpl. cbn in *.
    unfold DComma in x, y.
    refine (Square _ _ p q).
    { apply cat_postwhisker.
      exact (fmap2 F h1). }
    apply cat_prewhisker.
    exact (fmap2 G h2).
  Defined.


  Global Instance is01dcat_dhom_dcomma a b (x : DComma a) (y : DComma b)
    : Is01DCat (fun f : a $-> b => dHom f x y).
  Proof.
    snrapply Build_Is01DCat.
    { hnf. intros f p.
      simpl.
      (** Needs 2-functoriality *)
  Admitted.

  Global Instance is0dgpd_dhom_dcomma a b (x : DComma a) (y : DComma b)
    : Is0DGpd (fun f : a $-> b => dHom f x y).
  Proof.
  Admitted.

  Global Instance foo1 (a b c : A * B)
    (x : DComma a) (y : DComma b) (z : DComma c) 
    (g : b $-> c) (v : dHom g y z)
    : Is0DFunctor
        (fun ff : a $-> b => dHom ff x y) (fun h : a $-> c => dHom h x z)
        (cat_postcomp a g) (fun fff : a $-> b => dcat_postcomp DComma x fff v).
  Proof.
    snrapply Build_Is0DFunctor.
  Admitted.

  Global Instance foo2 (a b c : A * B)
    (x : DComma a) (y : DComma b) (z : DComma c) 
    (f : a $-> b) (u : dHom f x y)
    : Is0DFunctor (fun gg : b $-> c => dHom gg y z) (fun h : a $-> c => dHom h x z)
      (cat_precomp c f) (fun ggg : b $-> c => dcat_precomp DComma z ggg u).
  Proof.
  Admitted.

  Global Instance is1dcat_dcomma : Is1DCat DComma.
  Proof.
    snrapply Build_Is1DCat.
    1-5:exact _.
  Admitted.



  Definition Comma := sig DComma.

  Global Instance isgraph_comma : IsGraph Comma := _.
  Global Instance is01cat_comma : Is01Cat Comma := _.
  Global Instance is1cat_comma : Is1Cat Comma := _.

End Comma.






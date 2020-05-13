(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.Overture.
Require Import Basics.PathGroupoids.
Require Import Basics.Notations.
Require Import Basics.Contractible.
Require Import Basics.Equivalences.
Require Import WildCat.Core.
Require Import WildCat.TwoOneCat.
Require Import WildCat.NatTrans.

(** ** Indexed product of categories *)

(** Indexed products of categories inherit all their structure pointwise *)

Section Forall.

  (** Coq cannot generalize with a forall so we have to list out each structure. *)
  Context (A : Type) (B : A -> Type)
    `{forall a, IsGraph (B a)}
    `{forall a, Is01Cat (B a)}
    `{forall a, Is0Gpd (B a)}
    `{forall a, Is1Cat (B a)}
    `{forall a, Is1Gpd (B a)}
    `{forall a, Is21Cat (B a)}.

  Global Instance isgraph_forall : IsGraph (forall a, B a).
  Proof.
    srapply Build_IsGraph.
    intros x y; exact (forall (a : A), x a $-> y a).
  Defined.

  Global Instance is01cat_forall : Is01Cat (forall a, B a).
  Proof.
    srapply Build_Is01Cat.
    + intros x a; exact (Id (x a)).
    + intros x y z f g a; exact (f a $o g a).
  Defined.

  Global Instance is0gpd_forall : Is0Gpd (forall a, B a).
  Proof.
    constructor.
    intros f g p a; exact ((p a)^$).
  Defined.

  (** Here we show that the homs are 0-groupoids. *)
  Section ForallHom.

    Context (x y : forall a, B a).

    Global Instance isgraph_forall_hom : IsGraph (x $-> y).
    Proof.
      srapply Build_IsGraph.
      intros f g; exact (forall a, f a $== g a).
    Defined.

    Global Instance is01cat_forall_hom : Is01Cat (x $-> y).
    Proof.
      srapply Build_Is01Cat.
      - intros f a; apply Id.
      - intros f g h q p a; exact (p a $@ q a).
    Defined.

    Global Instance is0gpd_forall_hom : Is0Gpd (x $-> y).
    Proof.
      srapply Build_Is0Gpd.
      intros f g p a; exact (gpd_rev (p a)).
    Defined.

    (** Furthermore the 2-homs are also 0-groupoids. *)
    Section ForallHom2.

       Context (f g : x $-> y).

      Global Instance isgraph_forall_hom2 : IsGraph (f $== g).
      Proof.
        snrapply Build_IsGraph; intros p q.
        exact (forall a, p a $== q a).
      Defined.

      Global Instance is01cat_forall_hom2 : Is01Cat (f $== g).
      Proof.
        snrapply Build_Is01Cat.
        + intros p a.
          reflexivity.
        + intros p q r m n a.
          by transitivity (q a).
      Defined.

      Global Instance is0gpd_forall_hom2 : Is0Gpd (f $== g).
      Proof.
        snrapply Build_Is0Gpd.
        intros p q l a.
        exact (l a)^$.
      Defined.

    End ForallHom2.

  End ForallHom.

  (** The hom functor *)
  Section ForallHom_0Functor.

    Context (x y z : forall a, B a).

    Global Instance is0functor_forall_cat_postcomp (h : y $-> z)
      : Is0Functor (cat_postcomp x h).
    Proof.
      srapply Build_Is0Functor.
      intros f g p a.
      exact (h a $@L p a).
    Defined.

    Global Instance is0functor_forall_cat_precomp (h : x $-> y)
      : Is0Functor (cat_precomp z h).
    Proof.
      srapply Build_Is0Functor.
      intros f g p a.
      exact (p a $@R h a).
    Defined.

  End ForallHom_0Functor.

  (** The 2-hom functor on homs *)
  Section ForallHom2_Functor.

    Context (x y : forall a, B a) (p q r : x $-> y).

    Global Instance is0functor_forall_hom_cat_postcomp (g : q $-> r)
      : Is0Functor (cat_postcomp p g).
    Proof.
      snrapply Build_Is0Functor.
      intros l m t a.
      rapply cat_postwhisker.
      exact (t a).
    Defined.

    Global Instance is0functor_forall_hom_cat_precomp (f : p $-> q)
      : Is0Functor (cat_precomp r f).
    Proof.
      snrapply Build_Is0Functor.
      intros l m t a.
      rapply cat_prewhisker.
      exact (t a).
    Defined.

  End ForallHom2_Functor.

  (** Indexed products therefore inherit 1-cat structures from their factors. *)
  Global Instance is1cat_forall : Is1Cat (forall a, B a).
  Proof.
    snrapply Build_Is1Cat.
    1-5: exact _.
    + intros w x y z f g h a; apply cat_assoc.
    + intros x y f a; apply cat_idl.
    + intros x y f a; apply cat_idr.
  Defined.

  (** They also inherit their 1-groupoid structure. *)
  Global Instance is1gpd_forall : Is1Gpd (forall a, B a).
  Proof.
    snrapply Build_Is1Gpd.
    + intros x y f a.
      apply gpd_issect.
    + intros x y f a.
      apply gpd_isretr.
  Defined.

  (** Each hom is itself a category (in the presense of the factors being 2-categories *)
  Section ForallHom.

    Context (x y : forall a, B a).

    Global Instance is1cat_forall_hom : Is1Cat (x $-> y).
    Proof.
      snrapply Build_Is1Cat.
      1-5: exact _.
      + intros p q r s l m n a.
        apply cat_assoc.
      + intros p q l a.
        apply cat_idl.
      + intros p q l a.
        apply cat_idr.
    Defined.

    Global Instance is1gpd_forall_hom : Is1Gpd (x $-> y).
    Proof.
      snrapply Build_Is1Gpd.
      + intros p q l a.
        apply gpd_issect.
      + intros p q l a.
        apply gpd_isretr.
    Defined.

  End ForallHom.

  Section ForallHom_1Functor.

    Context (x y z : forall a, B a).

    Global Instance is1functor_forall_cat_postcomp (h : y $-> z)
      : Is1Functor (cat_postcomp x h).
    Proof.
      snrapply Build_Is1Functor.
      + intros p q l m t a.
        rapply fmap2.
        exact (t a).
      + intros p a. simpl.
        rapply fmap_id.
      + intros p q r l m a.
        rapply fmap_comp.
    Defined.

    Global Instance is1functor_forall_cat_precomp (h : x $-> y)
      : Is1Functor (cat_precomp z h).
    Proof.
      snrapply Build_Is1Functor.
      + intros p q l m t a.
        rapply fmap2.
        exact (t a).
      + intros p a. simpl.
        rapply fmap_id.
      + intros p q r l m a.
        rapply fmap_comp.
    Defined.

  End ForallHom_1Functor.

  (** Finally the 2-category structure is inherited form the factors. *)
  Global Instance is21cat_forall : Is21Cat (forall a, B a).
  Proof.
    snrapply Build_Is21Cat.
    1-4: exact _.
    + intros w x y z p q.
      snrapply Build_Is1Natural.
      intros l m t a.
      rapply (isnat _ (alnat:= is1natural_cat_assoc_l _ _ _ _ _ _)).
    + intros w x y z p q.
      snrapply Build_Is1Natural.
      intros l m t a.
      rapply (isnat _ (alnat:= is1natural_cat_assoc_m _ _ _ _ _ _) _).
    + intros w x y z p q.
      snrapply Build_Is1Natural.
      intros l m t a.
      rapply (isnat _ (alnat:= is1natural_cat_assoc_r _ _ _ _ _ _) _).
    + intros x y.
      snrapply Build_Is1Natural.
      intros l m t a.
      rapply (isnat _ (alnat:= is1natural_cat_idl _ _) _).
    + intros x y.
      snrapply Build_Is1Natural.
      intros l m t a.
      rapply (isnat _ (alnat:= is1natural_cat_idr _ _) _).
    + intros v w x y z p q r s a.
      rapply cat_pentagon.
    + intros x y z p q a.
      rapply cat_tril.
  Defined.

End Forall.




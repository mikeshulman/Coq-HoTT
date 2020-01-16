Require Import Basics.
Require Import WildCat.Core.

Section Comma.

  Context {A B C : Type}
    (F : A -> C) (G : B -> C).

  Record Comma `{IsGraph C} := {
    comma_domain : A;
    comma_codomain : B;
    comma_h : F comma_domain $-> G comma_codomain;
  }.

  Record CommaMor `{!IsGraph A, !IsGraph B, Is1Cat C,
    !Is0Functor F, !Is0Functor G} (X Y : Comma) :=
  {
    comma_mor_domain : comma_domain X $-> comma_domain Y;
    comma_mor_codomain : comma_codomain X $-> comma_codomain Y;
    comma_mor_h : 
      fmap G comma_mor_codomain $o comma_h X
      $== comma_h Y $o fmap F comma_mor_domain;
  }.
  
  Arguments comma_mor_domain {_ _ _ _ _ _ _ _}.
  Arguments comma_mor_codomain {_ _ _ _ _ _ _ _}.
  Arguments comma_mor_h {_ _ _ _ _ _ _ _}.

  Record Comma2Mor `{Is1Cat A, Is1Cat B, Is21Cat C, !Is0Functor F,
    !Is1Functor F, !Is0Functor G, !Is1Functor G} {X Y : Comma}
    (f g : CommaMor X Y) :=
  {
    comma_2mor_domain : comma_mor_domain f $== comma_mor_domain g;
    
    comma_2mor_codomain : comma_mor_codomain f $== comma_mor_codomain g;
    
    comma_2mor_h
      : (comma_h Y) $@L (fmap2 F comma_2mor_domain) $o comma_mor_h f
      $== comma_mor_h g $o (fmap2 G comma_2mor_codomain) $@R (comma_h X);
  }.

  Section Cat.

    Context
      `{Is1Cat A, Is1Cat B, Is21Cat C,
        !Is0Functor F, !Is1Functor F,
        !Is0Functor G, !Is1Functor G}.

    Global Instance is01cat_comma : Is01Cat Comma.
    Proof.
      serapply Build_Is01Cat.
      + exact CommaMor.
      + intros [a b h].
        serapply Build_CommaMor.
        1,2: exact (Id _).
        refine (fmap11 cat_comp (fmap_id G _) (Id _) $@ _).
        refine (cat_idl h $@ _).
        symmetry.
        refine (fmap11 cat_comp (Id _) (fmap_id _ _) $@ _).
        apply cat_idr.
      + intros [a b h] [a' b' h'] [a'' b'' h''].
        intros [fa fb fh] [ga gb gh].
        cbn in *.
        serapply Build_CommaMor.
        1: exact (fa $o ga).
        1: exact (fb $o gb).
        refine (fmap_comp _ _ _ $@R h $@ _).
        refine (cat_assoc _ _ _ $@ _).
        refine (_ $@L gh $@ _).
        refine ((cat_assoc _ _ _)^$ $@ _).
        refine (fh $@R _ $@ _).
        refine (cat_assoc _ _ _ $@ _^$).
        refine (_ $@L fmap_comp _ _ _).
    Defined.

    Global Instance is01cat_commamor : forall a b : Comma, Is01Cat (a $-> b).
    Proof.
      intros x y.
      serapply Build_Is01Cat.
      + exact Comma2Mor.
      + intro a.
        serapply (Build_Comma2Mor _ _ _ _ _ _ _ _).
        1,2: exact (Id _).
        cbn.
    Admitted.

    Global Instance is0gpd_commamor : forall a b : Comma, Is0Gpd (a $-> b).
    Proof.
    Admitted.

    Global Instance is0functor_commamor_comp
      : forall a b c : Comma, Is0Functor (uncurry (@cat_comp _ _ a b c)).
    Proof.
    Admitted.

    Global Instance is0coh21cat_comma : Is1Cat Comma.
    Proof.
      serapply Build_Is1Cat.
    Admitted.

  End Cat.

End Comma.






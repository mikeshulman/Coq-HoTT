Require Import Basics.
Require Import WildCat.Core.
Require Import WildCat.Prod.
Require Import WildCat.TwoOneCat.
Require Import WildCat.Square.

Section Comma.

  Context {A B C : Type}
    (F : A -> C) (G : B -> C).

  Record Comma `{IsGraph C} := {
    comma_domain : A;
    comma_codomain : B;
    comma_h : F comma_domain $-> G comma_codomain;
  }.

  Record CommaMor `{!IsGraph A, !IsGraph B, Is1Cat C, !Is0Functor F, !Is0Functor G}
    (X Y : Comma) :=
  {
    comma_mor_domain : comma_domain X $-> comma_domain Y;
    comma_mor_codomain : comma_codomain X $-> comma_codomain Y;
    comma_mor_h : Square (fmap F comma_mor_domain) (fmap G comma_mor_codomain)
      (comma_h X) (comma_h Y);
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
    
    comma_2mor_h : Square ((comma_h Y) $@L (fmap2 F comma_2mor_domain))
          ((fmap2 G comma_2mor_codomain) $@R (comma_h X))
          (comma_mor_h f) (comma_mor_h g);
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
      + intros abh.
        serapply Build_CommaMor.
        1,2: exact (Id _).
        refine (vconcatL (fmap_id F _) _).
        refine (vconcatR _ (fmap_id G _)).
        apply hrefl.
      + intros abh abh' abh''.
        intros [fa fb fh] [ga gb gh].
        serapply Build_CommaMor.
        1: exact (fa $o ga).
        1: exact (fb $o gb).
        refine (vconcatL (fmap_comp F _ _) _).
        refine (vconcatR _ (fmap_comp G _ _)).
        exact (hconcat gh fh).
    Defined.

    Axiom foo : Empty.
    Ltac admit := apply Empty_ind, foo.

    Global Instance is01cat_commamor : forall a b : Comma, Is01Cat (a $-> b).
    Proof.
      intros x y.
      serapply Build_Is01Cat.
      + exact Comma2Mor.
      + intro a.
        serapply (Build_Comma2Mor _ _ _ _ _ _ _ _).
        1,2: exact (Id _).
    Admitted.

    Global Instance is0gpd_commamor : forall a b : Comma, Is0Gpd (a $-> b).
    Proof.
      intros x y.
      serapply Build_Is0Gpd.
      (* 
      intros a b [p q h].
      unshelve econstructor.
      1: exact p^$.
      1: exact q^$.
      cat_prewhisker
      
      serapply Build_CommaMor. *)
    Admitted.

    Global Instance is0functor_commamor_postcomp
      : forall (a b c : Comma) (g : b $-> c), Is0Functor (cat_postcomp a g).
    Proof.
    Admitted.

    Global Instance is0functor_commamor_precomp
      : forall (a b c : Comma) (f : a $-> b), Is0Functor (cat_precomp c f).
    Proof.
    Admitted.

    Global Instance is1cat_comma : Is1Cat Comma.
    Proof.
      serapply Build_Is1Cat.
      { intros a b c d f g h.
    Admitted.

    Global Instance is0coh21cat_comma : Is1Cat Comma.
    Proof.
      serapply Build_Is1Cat.
    Admitted.

  End Cat.

End Comma.






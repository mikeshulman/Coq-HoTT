Require Export Basics.
Require Export WildCat.Core.
Require Export WildCat.Equiv.
Require Export WildCat.Forall.
Require Export WildCat.Paths.
Require Export WildCat.TwoOneCat.

(** ** The category of types *)

Global Instance isgraph_type : IsGraph Type
  := Build_IsGraph Type (fun a b => a -> b).

Global Instance is01cat_type : Is01Cat Type.
Proof.
  econstructor.
  + intro; exact idmap.
  + exact (fun a b c g f => g o f).
Defined.

Global Instance isgraph_arrow {A B : Type} : IsGraph (A $-> B).
Proof.
  snrapply isgraph_forall.
  intro.
  apply isgraph_paths.
Defined.

Global Instance is01cat_arrow {A B : Type} : Is01Cat (A $-> B).
Proof.
  apply is01cat_forall.
  intro.
  apply is01cat_paths.
Defined.

Global Instance is0gpd_arrow {A B : Type}: Is0Gpd (A $-> B).
Proof.
  apply is0gpd_forall.
  intro.
  apply is0gpd_paths.
Defined.

Global Instance is0functor_type_postcomp {A B C : Type} (h : B $-> C)
  : Is0Functor (cat_postcomp A h).
Proof.
  apply Build_Is0Functor.
  intros f g p a; exact (ap h (p a)).
Defined.

Global Instance is0functor_type_precomp {A B C : Type} (h : A $-> B):
  Is0Functor (cat_precomp C h).
Proof.
  apply Build_Is0Functor.
  intros f g p a; exact (p (h a)).
Defined.

Global Instance is1cat_strong_type : Is1Cat_Strong Type.
Proof.
  srapply Build_Is1Cat_Strong; cbn; intros; reflexivity.
Defined.

Global Instance hasmorext_type `{Funext} : HasMorExt Type.
Proof.
  srapply Build_HasMorExt.
  intros A B f g; cbn in *.
  refine (isequiv_homotopic (@apD10 A (fun _ => B) f g) _).
  intros p.
  destruct p; reflexivity.
Defined.

Global Instance hasequivs_type : HasEquivs Type.
Proof.
  srefine (Build_HasEquivs Type _ _ _ Equiv (@IsEquiv) _ _ _ _ _ _ _ _); intros A B.
  all:intros f.
  - exact f.
  - exact _.
  - apply Build_Equiv.
  - intros; reflexivity.
  - intros; exact (f^-1).
  - cbn. intros ?; apply eissect.
  - cbn. intros ?; apply eisretr.
  - intros g r s; refine (isequiv_adjointify f g r s).
Defined.

Definition catie_isequiv {A B : Type} {f : A $-> B}
       `{IsEquiv A B f} : CatIsEquiv f.
Proof.
  assumption.
Defined.

Hint Immediate catie_isequiv : typeclass_instances.

Global Instance isinitial_zero : IsInitial Empty.
Proof.
  intro A.
  exists (Empty_rec _).
  intros g.
  rapply Empty_ind.
Defined.

Global Instance isterminal_unit : IsTerminal Unit.
Proof.
  intros A.
  exists (fun _ => tt).
  intros f x.
  by destruct (f x).
Defined.

(** Type is a wild (2,1)-category *)

Global Instance is1cat_arrow {A B : Type} : Is1Cat (A $-> B).
Proof.
  apply is1cat_forall.
  intro.
  apply is1cat_paths.
Defined.

Global Instance is1gpd_arrow {A B : Type} : Is1Gpd (A $-> B).
Proof.
  apply is1gpd_forall.
  intro.
  apply is1gpd_paths.
Defined.

Global Instance is21cat_type : Is21Cat Type.
Proof.
  snrapply Build_Is21Cat.
  1-2: exact _.
  { intros x y z g.
    snrapply Build_Is1Functor.
    { intros a b f h p w.
      cbn; rapply ap.
      rapply p. }
    { intros a.
      reflexivity. }
    intros a b c f h w.
    cbn; rapply ap_pp. }
  { intros x y z g.
    snrapply Build_Is1Functor.
    { intros a b f h p w.
      rapply p. }
    { intros a.
      reflexivity. }
    intros a b c f h w.
    reflexivity. }
  + intros w x y z p q.
    snrapply Build_Is1Natural.
    intros l m t a.
    cbn; hott_simpl.
  + intros w x y z p q.
    snrapply Build_Is1Natural.
    intros l m t a.
    cbn; hott_simpl.
  + intros w x y z p q.
    snrapply Build_Is1Natural.
    intros l m t a.
    cbn; hott_simpl.
    apply ap_compose.
  + intros x y.
    snrapply Build_Is1Natural.
    intros l m t a.
    cbn; hott_simpl.
  + intros x y.
    snrapply Build_Is1Natural.
    intros l m t a.
    cbn; hott_simpl.
  + intros v w x y z p q r s a.
    cbn; hott_simpl.
  + intros x y z p q a.
    cbn; hott_simpl.
Defined.

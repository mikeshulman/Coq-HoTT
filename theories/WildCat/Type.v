Require Export Basics.
Require Export WildCat.Core.
Require Export WildCat.Equiv.

(** ** The category of types *)

Global Instance is0coh1cat_type : Is0Coh1Cat Type
  := Build_Is0Coh1Cat Type (fun a b => a -> b)
                      (fun a => idmap) (fun a b c g f => g o f).

Global Instance is0coh1cat_arrow {A B : Type}: Is0Coh1Cat (A $-> B)
  := Build_Is0Coh1Cat _ (fun f g => f == g) (fun f a => idpath)
                      (fun f g h p q a => q a @ p a).

Global Instance is0coh1gpd_arrow {A B : Type}: Is0Coh1Gpd (A $-> B).
Proof.
  apply Build_Is0Coh1Gpd.
  intros f g p a ; exact (p a)^.
Defined.

Global Instance is0coh1functor_comp {A B C : Type}:
  Is0Coh1Functor (uncurry (@cat_comp Type _ A B C)).
Proof.
  apply Build_Is0Coh1Functor.
  intros [f g] [f' g'] [p p'] a ;
    exact (p (g a) @ ap f' (p' a)).
Defined.

Global Instance is0coh21cat_type : Is0Coh21Cat Type.
Proof.
  rapply (Build_Is0Coh21Cat Type _ _ (fun a b => is0coh1gpd_arrow)).
Defined.

Global Instance is1coh1cat_strong_type : Is1Coh1Cat_Strong Type.
Proof.
  srapply Build_Is1Coh1Cat_Strong'; cbn; intros; reflexivity.
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
  srefine (Build_HasEquivs Type _ _ Equiv (@IsEquiv) _ _ _ _ _ _ _ _); intros A B.
  all:intros f.
  - exact f.
  - exact _.
  - apply Build_Equiv.
  - intros; reflexivity.
  - intros; exact (f^-1).
  - cbn. intros ? x; apply eissect.
  - cbn. intros ? x; apply eisretr.
  - intros g r s; refine (isequiv_adjointify f g r s).
Defined.

Definition catie_isequiv {A B : Type} {f : A $-> B}
       `{IsEquiv A B f} : CatIsEquiv f.
Proof.
  assumption.
Defined.

Hint Immediate catie_isequiv : typeclass_instances.

Require Export Basics.
Require Export WildCat.Core.
Require Export WildCat.NatTrans.
Require Export WildCat.TwoOneCat.

(** * Path groupoids as wild categories *)

(** Not global instances for now *)
Local Instance isgraph_paths (A : Type) : IsGraph A.
Proof.
  constructor.
  intros x y; exact (x = y).
Defined.

Local Instance is01cat_paths (A : Type) : Is01Cat A.
Proof.
  unshelve econstructor.
  - intros a; reflexivity.
  - intros a b c q p; exact (p @ q).
Defined.

Local Instance is0gpd_paths (A : Type) : Is0Gpd A.
Proof.
  constructor.
  intros x y p; exact (p^).
Defined.

Local Instance is1cat_paths (A : Type) : Is1Cat A.
Proof.
  econstructor.
  { intros a b c g.
    econstructor.
    intros p q r.
    exact (whiskerR r g). }
  { intros a b c f.
    econstructor.
    intros p q r.
    exact (whiskerL f r). }
  { intros a b c d f g h.
    apply concat_p_pp. }
  { intros a b f.
    apply concat_p1. }
  intros a b f.
  apply concat_1p.
Defined.

Local Instance is1gpd_paths (A : Type) : Is1Gpd A.
Proof.
  econstructor.
  { intros a b f.
    apply concat_pV. }
  intros a b f.
  apply concat_Vp.
Defined.

Local Instance is1functor_paths_cat_postcomp (A : Type) (a b c : A) (g : b $-> c)
  : Is1Functor (cat_postcomp a g).
Proof.
  snrapply Build_Is1Functor.
  { intros p q r s t.
    by destruct t. }
  1: reflexivity.
  intros p q r s t.
  apply whiskerR_pp.
Defined.

Local Instance is1functor_pathS_cat_precomp (A : Type) (a b c : A) (f : a $-> b)
  : Is1Functor (cat_precomp c f).
Proof.
  snrapply Build_Is1Functor.
  { intros p q r s t.
    by destruct t. }
  1: reflexivity.
  intros p q r s t.
  apply whiskerL_pp.
Defined.

Definition whiskerL_L_Lpp {A : Type} {a b c d : A} {f : a = b} {g : b = c} {p q : c = d} (r : p = q)
  : whiskerL f (whiskerL g r) @ concat_p_pp f g q = concat_p_pp f g p @ whiskerL (f @ g) r.
Proof.
  by destruct f, g, r, p.
Defined.

Definition whiskerL_R_RL {A : Type} {a b c d : A} {f : a = b} {h : c = d} {p q : b = c} (r : p = q)
  : whiskerL f (whiskerR r h) @ concat_p_pp f q h = concat_p_pp f p h @ whiskerR (whiskerL f r) h.
Proof.
  by destruct f, h, r, p.
Defined.

Local Instance is21cat_paths (A : Type) : Is21Cat A.
Proof.
  econstructor.
  1-3: exact _.
  { intros a b c d f g.
    snrapply Build_Is1Natural.
    intros p q r.
    apply whiskerL_L_Lpp. }
  { intros a b c d f h.
    snrapply Build_Is1Natural.
    intros p q r.
    cbn in *.
    apply whiskerL_R_RL. }
  { intros a b c d g h.
    snrapply Build_Is1Natural.
    intros p q r.
    cbn in *.
    destruct g, h, r, p.
    reflexivity. }
  { intros a b.
    snrapply Build_Is1Natural.
    intros p q r.
    cbn.
(*     apply whiskerR_p1. *)
    destruct r, p.
    reflexivity. }
  { intros a b.
    snrapply Build_Is1Natural.
    intros p q r.
    cbn.
(*     apply whiskerL_1p. *)
    destruct r, p.
    reflexivity. }
  { (** Pentagon *)
    cbn.
    intros a b c d e f g h k.
    refine (concat_p_pp _ _ _ @ _).
    apply pentagon. }
  intros a b c f g.
  cbn.
  destruct f, g.
  reflexivity.
Defined.


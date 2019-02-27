Require Import HoTT.Basics HoTT.Types HoTT.HIT.Truncations.

(* Doesn't use = *)
Class IsWildProp (X : Type) := 
  trans_iswildprop : forall (P : X -> Type) (x1 x2 : X), P x1 -> P x2.

(* Uses = *)
Definition ishprop_iswildprop (X : Type) `{IsWildProp X} : IsHProp X.
Proof.
  apply hprop_allpath; intros x1 x2.
  exact (trans_iswildprop (fun x => (x1 = x)) x1 x2 idpath).
Defined.

(* Uses = *)
Definition iswildprop_ishprop (X : Type) `{IsHProp X} : IsWildProp X.
Proof.
  intros P x1 x2 p.
  exact (path_ishprop x1 x2 # p).
Defined.

(* Doesn't use = *)
Definition wild_merelyeq {X : Type} (x1 x2 : X) : Type
  := forall (P : X -> Type), (forall x, IsWildProp (P x)) -> (P x1 -> P x2).

(* Uses = *)
Global Instance ishprop_wild_merelyeq `{Funext} {X : Type} (x1 x2 : X)
  : IsHProp (wild_merelyeq x1 x2).
Proof.
  unfold wild_merelyeq.
  refine (@trunc_forall _ (X -> Type) _ _ _); intros P.
  refine (@trunc_forall _ (forall x, IsWildProp (P x)) _ _ _); intros ?.
  pose (ishprop_iswildprop (P x2)).
  exact _.
Defined.
  
(* Uses = *)
Definition to_wild_merelyeq `{Funext} {X : Type} (x1 x2 : X) (p : merely (x1 = x2))
  : wild_merelyeq x1 x2.
Proof.
  intros P ?.
  pose (ishprop_iswildprop (P x2)).
  strip_truncations.
  destruct p.
  intros z; exact z.
Defined.

(* Uses = *)
Definition from_wild_merelyeq `{Funext} {X : Type} (x1 x2 : X) (p : wild_merelyeq x1 x2)
  : merely (x1 = x2).
Proof.
  refine (p (fun x => merely (x1 = x)) _ (tr idpath)).
  exact (fun x => iswildprop_ishprop _).
Defined.

(* Uses = *)
Definition wild_merelyeq_equiv_merelyeq `{Funext} {X : Type} (x1 x2 : X)
  : wild_merelyeq x1 x2 <~> merely (x1 = x2)
  := equiv_iff_hprop (from_wild_merelyeq x1 x2) (to_wild_merelyeq x1 x2).

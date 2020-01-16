(* -*- mode: coq; mode: visual-line -*- *)
Require Import Basics Types UnivalenceImpliesFunext.
Require Import Pointed.Core.
Require Import WildCat.
Require Import pHomotopy pMap pEquiv Loops.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

(** * pType as a wild category *)

Global Instance is01cat_ptype : Is01Cat pType
  := Build_Is01Cat pType pMap (@pmap_idmap) (@pmap_compose).

Global Instance is01cat_pmap (A : pType) (P : pFam A) : Is01Cat (pForall A P).
Proof.
  srapply (Build_Is01Cat _ (@pHomotopy A P)).
  - reflexivity.
  - intros a b c f g; transitivity b; assumption.
Defined.

Global Instance is0gpd_pmap (A : pType) (P : pFam A) : Is0Gpd (pForall A P).
Proof.
  srapply Build_Is0Gpd.
  intros; symmetry; assumption.
Defined.

Global Instance is1cat_ptype : Is1Cat pType.
Proof.
  simple refine (Build_Is1Cat _ _ _ _ _ _ _ _); try exact _.
  - intros A B C; rapply Build_Is0Functor.
    intros [f1 f2] [g1 g2] [p q]; cbn.
    transitivity (f1 o* g2).
    + apply pmap_postwhisker; assumption.
    + apply pmap_prewhisker; assumption.
  - intros ? ? ? ? f g h; exact (pmap_compose_assoc h g f).
  - intros ? ? f; exact (pmap_postcompose_idmap f).
  - intros ? ? f; exact (pmap_precompose_idmap f).
Defined.

Global Instance hasmorext_ptype `{Funext} : HasMorExt pType.
Proof.
  srapply Build_HasMorExt; intros A B f g.
  refine (isequiv_homotopic (equiv_path_pmap f g)^-1 _).
  intros []; reflexivity.
Defined.


Global Instance hasequivs_ptype : HasEquivs pType.
Proof.
  srapply (Build_HasEquivs _ _ _ pEquiv (fun A B f => IsEquiv f));
    intros A B f; cbn; intros.
  - exact f.
  - exact _.
  - exact (Build_pEquiv _ _ f _).
  - reflexivity.
  - exact ((Build_pEquiv _ _ f _)^-1*).
  - apply peissect.
  - cbn. refine (peisretr (Build_pEquiv _ _ f _)).
  - rapply (isequiv_adjointify f g).
    + intros x; exact (r x).
    + intros x; exact (s x).
Defined.

Global Instance isunivalent_ptype `{Univalence} : IsUnivalent1Cat pType.
Proof.
  srapply Build_IsUnivalent1Cat; intros A B.
  refine (isequiv_homotopic (equiv_path_ptype A B)^-1 _).
  intros []; apply path_pequiv.
  cbn.
  srefine (Build_pHomotopy _ _).
  - intros x; reflexivity.
  - cbn.
    (* Some messy path algebra here. *)
Abort.

Global Instance is0functor_pointed_type : Is0Functor pointed_type.
Proof.
  apply Build_Is0Functor. intros. exact f.
Defined.
  
Global Instance is1functor_pointed_type : Is1Functor pointed_type.
Proof.
  apply Build_Is1Functor.
  + intros ? ? ? ? h. exact h.
  + intros. reflexivity.
  + intros. reflexivity.
Defined.

Global Instance is0functor_loops
  : Is0Functor loops.
Proof.
  apply Build_Is0Functor. intros. exact (loops_functor f).
Defined.

Global Instance is1functor_loops : Is1Functor loops.
Proof.
  apply Build_Is1Functor.
  + intros ? ? ? ? h. exact (loops_2functor h).
  + intros. apply loops_functor_idmap.
  + intros. apply loops_functor_compose.
Defined.

Global Instance is0functor_iterated_loops (n : nat)
  : Is0Functor (iterated_loops n).
Proof.
  apply Build_Is0Functor. intros. exact (iterated_loops_functor n f).
Defined.

Global Instance is1functor_iterated_loops (n : nat)
  : Is1Functor (iterated_loops n).
Proof.
  apply Build_Is1Functor.
  + intros ? ? ? ? h. exact (iterated_loops_2functor n h).
  + intros. apply iterated_loops_functor_idmap.
  + intros. apply iterated_loops_functor_compose.
Defined.

Global Instance is1natural_loops_inv : Is1Natural loops loops loops_inv.
Proof.
  apply Build_Is1Natural. intros A B f.
  serapply Build_pHomotopy.
  + intros p. refine (inv_Vp _ _ @ whiskerR _ (point_eq f) @ concat_pp_p _ _ _).
    refine (inv_pp _ _ @ whiskerL (point_eq f)^ (ap_V f p)^).
  + pointed_reduce. pointed_reduce. reflexivity.
Defined.

(* TODO: generalize to wild categories with 0 object. *)
Definition hconst_square {A B C D : pType} {f : A $-> B} {g : C $-> D} : 
  Square pConst pConst f g :=
  precompose_pconst g $@ (postcompose_pconst f)^$.

Definition vconst_square {A B C D : pType} {f : A $-> B} {g : C $-> D} : 
  Square f g pConst pConst :=
  postcompose_pconst f $@ (precompose_pconst g)^$.

(* TODO: show that loops_functor and iterated_loops_functor are 1-functors. *)
(* TODO: show that loops_inv is a natural transformation. *)

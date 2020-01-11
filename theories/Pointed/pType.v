(* -*- mode: coq; mode: visual-line -*- *)
Require Import Basics Types.
Require Import Pointed.Core.
Require Import WildCat.
Require Import pHomotopy pMap pEquiv.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

Global Instance is0coh1cat_ptype : Is0Coh1Cat pType
  := Build_Is0Coh1Cat pType pMap (@pmap_idmap) (@pmap_compose).
  
  (** pointed homotopy stuff. *)
  
  Global Instance is0coh1cat_pmap (A B : pType) : Is0Coh1Cat (A ->* B).
Proof.
  srapply (Build_Is0Coh1Cat (A ->* B) (@pHomotopy A B)).
  - reflexivity.
  - intros a b c f g; transitivity b; assumption.
Defined.

Global Instance is0coh1gpd_pmap (A B : pType) : Is0Coh1Gpd (A ->* B).
Proof.
  srapply Build_Is0Coh1Gpd.
  intros; symmetry; assumption.
Defined.

Global Instance is0coh2cat_ptype : Is0Coh21Cat pType.
Proof.
  rapply Build_Is0Coh21Cat; try exact _.
  intros A B C; rapply Build_Is0Coh1Functor; intros [f1 f2] [g1 g2] [p q]; cbn.
  transitivity (f1 o* g2).
  - apply pmap_postwhisker; assumption.
  - apply pmap_prewhisker; assumption.
Defined. 





Global Instance is1coh1cat_ptype : Is1Coh1Cat pType.
Proof.
  srapply Build_Is1Coh1Cat.
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
  (* TODO: Borken *)
Admitted.
(*
  srapply (Build_HasEquivs _ _ _ pEquiv (fun A B f => f) (fun A B f => f^-1* ));
    cbn; intros A B f.
  - apply peissect.
  - apply peisretr.
  - apply pequiv_adjointify.
  - reflexivity.
Defined.
*)

Global Instance isunivalent_ptype `{Univalence} : IsUnivalent1Cat pType.
Proof.
  srapply Build_IsUnivalent1Cat; intros A B.
Admitted.
(*
  refine (isequiv_homotopic (equiv_path_ptype A B)^-1 _).
  intros []; apply path_pequiv.
  cbn.
  srefine (Build_pHomotopy _ _).
  - intros x; reflexivity.
  - cbn.
    admit.
*)

Global Instance is0coh1functor_pmap : Is0Coh1Functor (uncurry pMap).
Proof.
  serapply Build_Is0Coh1Functor. 
  

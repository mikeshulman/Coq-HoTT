Require Import Basics.
Require Import Types.
<<<<<<< HEAD
Require Import Pointed.Core.
Require Import UnivalenceImpliesFunext.
Require Import WildCat.
=======
Require Import Pointed.Core Pointed.pMap Pointed.pHomotopy.
>>>>>>> master

Local Open Scope pointed_scope.

(* The pointed identity is a pointed equivalence *)
Definition pequiv_pmap_idmap {A} : A <~>* A
  := Build_pEquiv _ _ pmap_idmap _.

(* pointed equivalence is a reflexive relation *)
Global Instance pequiv_reflexive : Reflexive pEquiv.
Proof.
  intro; apply pequiv_pmap_idmap.
Defined.

(* We can probably get rid of the following notation, and use ^-1$ instead. *)
Notation "f ^-1*" := (@cate_inv pType _ _ _ hasequivs_ptype _ _ f) : pointed_scope.

(* pointed equivalence is a symmetric relation *)
Global Instance pequiv_symmetric : Symmetric pEquiv.
Proof.
  intros ? ?; apply pequiv_inverse.
Defined.

(* pointed equivalences compose. *)
Definition pequiv_compose {A B C : pType} (f : A <~>* B) (g : B <~>* C)
  : A <~>* C
  := g $oE f.

(* pointed equivalence is a transitive relation *)
Global Instance pequiv_transitive : Transitive pEquiv.
Proof.
  intros ? ? ?; apply pequiv_compose.
Defined.

Notation "g o*E f" := (pequiv_compose f g) : pointed_scope.

Definition issig_pequiv (A B : pType)
  : { f : A ->* B & IsEquiv f } <~> (A <~>* B).
Proof.
  issig.
Defined.

(* Two pointed equivalences are equal if their underlying pointed functions are pointed homotopic. *)
Definition equiv_path_pequiv `{Funext} {A B : pType} (f g : A <~>* B)
  : (f ==* g) <~> (f = g).
Proof.
  transitivity ((issig_pequiv A B)^-1 f = (issig_pequiv A B)^-1 g).
  - refine (equiv_path_sigma_hprop _ _ oE _).
    apply (equiv_path_pmap f g).
  - symmetry; exact (equiv_ap' (issig_pequiv A B)^-1 f g).
Defined.

Definition path_pequiv `{Funext} {A B : pType} (f g : A <~>* B)
  : (f ==* g) -> (f = g)
  := fun p => equiv_path_pequiv f g p.

(* The record for pointed equivalences is equivalently a different sigma type *)
Definition issig_pequiv' (A B : pType)
  : { f : A <~> B & f (point A) = point B } <~> (A <~>* B).
Proof.
  make_equiv.
Defined.

(* Sometimes we wish to construct a pEquiv from an equiv and a proof that it is pointed *)
Definition Build_pEquiv' {A B : pType} (f : A <~> B)
  (p : f (point A) = point B)
  : A <~>* B := Build_pEquiv _ _ (Build_pMap _ _ f p) _.

Definition path_ptype `{Univalence} {A B : pType} : (A <~>* B) -> A = B
  := equiv_path_ptype A B.

Definition pequiv_path {A B : pType} : (A = B) -> (A <~>* B).
Proof.
  intros p; apply (ap issig_ptype^-1) in p.
  srefine (Build_pEquiv' (equiv_path A B p..1) p..2).
Defined.

<<<<<<< HEAD
=======
(* A pointed version of Sect (sometimes useful for proofs of some equivalences) *)
Definition pSect {A B : pType} (s : A ->* B) (r : B ->* A)
  := r o* s ==* pmap_idmap.

Arguments pSect _ _ / _ _.

(* A pointed equivalence is a section of its inverse *)
Definition peissect {A B : pType} (f : A <~>* B) : pSect f f^-1*.
Proof.
  pointed_reduce_pmap f.
  srefine (Build_pHomotopy _ _).
  1: apply (eissect f).
  unfold moveR_equiv_V; cbn.
  refine (concat_p1 _ @ (concat_1p _)^ @ (concat_1p _)^).
Defined.

(* A pointed equivalence is a retraction of its inverse *)
Definition peisretr {A B : pType} (f : A <~>* B) : pSect f^-1* f.
Proof.
  srefine (Build_pHomotopy _ _).
  1: apply (eisretr f).
  pointed_reduce_pmap f.
  unfold moveR_equiv_V; cbn.
  apply whiskerR.
  refine (_ @ (ap _ (concat_1p _))^).
  apply eisadj.
Defined.

>>>>>>> master
(* A version of equiv_adjointify for pointed equivalences
  where all data is pointed. There is a lot of unecessery data here
  but sometimes it is easier to prove equivalences using this. *)
Definition pequiv_adjointify {A B : pType} (f : A ->* B) (f' : B ->* A)
  (r : pSect f' f) (s : pSect f f') : A <~>* B
  := (Build_pEquiv _ _ f (isequiv_adjointify f f' r s)).

(* In some situations you want the back and forth maps to be pointed
   but not the sections *)
Definition pequiv_adjointify' {A B : pType} (f : A ->* B) (f' : B ->* A)
  (r : Sect f' f) (s : Sect f f') : A <~>* B
  := (Build_pEquiv _ _ f (isequiv_adjointify f f' r s)).

(** Pointed versions of [moveR_equiv_M] and friends. *)
Definition moveR_pequiv_Mf {A B C} (f : B <~>* C) (g : A ->* B) (h : A ->* C)
           (p : g ==* f^-1* o* h)
  : (f o* g ==* h).
Proof.
  refine (pmap_postwhisker f p @* _).
  refine ((pmap_compose_assoc _ _ _)^* @* _).
  refine (pmap_prewhisker h (peisretr f) @* _).
  apply pmap_postcompose_idmap.
Defined.

Definition moveL_pequiv_Mf {A B C} (f : B <~>* C) (g : A ->* B) (h : A ->* C)
           (p : f^-1* o* h ==* g)
  : (h ==* f o* g).
Proof.
  refine (_ @* pmap_postwhisker f p).
  refine (_ @* (pmap_compose_assoc _ _ _)).
  refine ((pmap_postcompose_idmap _)^* @* _).
  apply pmap_prewhisker.
  symmetry; apply peisretr.
Defined.

Definition moveL_pequiv_Vf {A B C} (f : B <~>* C) (g : A ->* B) (h : A ->* C)
           (p : f o* g ==* h)
  : g ==* f^-1* o* h.
Proof.
  refine (_ @* pmap_postwhisker f^-1* p).
  refine (_ @* (pmap_compose_assoc _ _ _)).
  refine ((pmap_postcompose_idmap _)^* @* _).
  apply pmap_prewhisker.
  symmetry; apply peissect.
Defined.

Definition moveR_pequiv_Vf {A B C} (f : B <~>* C) (g : A ->* B) (h : A ->* C)
           (p : h ==* f o* g)
   : f^-1* o* h ==* g.
Proof.
  refine (pmap_postwhisker f^-1* p @* _).
  refine ((pmap_compose_assoc _ _ _)^* @* _).
  refine (pmap_prewhisker g (peissect f) @* _).
  apply pmap_postcompose_idmap.
Defined.

Definition moveR_pequiv_fV {A B C} (f : B ->* C) (g : A <~>* B) (h : A ->* C)
           (p : f o* g ==* h)
  : (f ==* h o* g^-1*).
Proof.
  refine (_ @* pmap_prewhisker g^-1* p).
  refine (_ @* (pmap_compose_assoc _ _ _)^*).
  refine ((pmap_precompose_idmap _)^* @* _).
  apply pmap_postwhisker.
  symmetry; apply peisretr.
Defined.

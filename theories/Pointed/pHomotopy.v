Require Import Basics.
Require Import WildCat.
Require Import Types.
Require Import Pointed.Core.

Local Open Scope pointed_scope.

(* pointed homotopy is a reflexive relation *)
Global Instance phomotopy_reflexive {A B} : Reflexive (@pHomotopy A B).
Proof.
  intro.
  serapply Build_pHomotopy.
  + intro. reflexivity.
  + apply concat_1p.
Defined.

(** ** Whiskering of pointed homotopies by pointed functions *)

Definition pmap_postwhisker {A B C : pType} {f g : A ->* B}
  (h : B ->* C) (p : f ==* g) : h o* f ==* h o* g.
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros a; apply ap, p.
  - reflexivity.
Qed.

Definition pmap_prewhisker {A B C : pType} (f : A ->* B)
  {g h : B ->* C} (p : g ==* h) : g o* f ==* h o* f.
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros a; apply p.
  - refine (concat_p1 _ @ (concat_1p _)^).
Qed.

(** ** Composition of pointed homotopies *)

Definition phomotopy_compose {A B : pType} {f g h : A ->* B}
  (p : f ==* g) (q : g ==* h) : f ==* h.
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros x; exact (p x @ q x).
  - apply concat_p1.
Qed.

Infix "@*" := phomotopy_compose : pointed_scope.

(* pointed homotopy is a transitive relation *)
Global Instance phomotopy_transitive {A B} : Transitive (@pHomotopy A B)
  := @phomotopy_compose A B.

Definition phomotopy_inverse {A B : pType} {f g : A ->* B}
: (f ==* g) -> (g ==* f).
Proof.
  intros p; pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros x; exact ((p x)^).
  - apply concat_Vp.
Qed.

(* pointed homotopy is a symmetric relation *)
Global Instance phomotopy_symmetric {A B} : Symmetric (@pHomotopy A B)
  := @phomotopy_inverse A B.


Notation "p ^*" := (phomotopy_inverse p) : pointed_scope.

Definition issig_phomotopy {A B : pType} (f g : A ->* B)
: { p : f == g & p (point A) @ point_eq g = point_eq f } <~> (f ==* g).
Proof.
  issig.
Defined.

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

Global Instance is0coh2cat_ptype : Is0Coh2Cat pType.
Proof.
  rapply Build_Is0Coh2Cat; try exact _.
  intros A B C; rapply Build_Is0Coh1Functor; intros [f1 f2] [g1 g2] [p q]; cbn.
  transitivity (f1 o* g2).
  - apply pmap_postwhisker; assumption.
  - apply pmap_prewhisker; assumption.
Defined.

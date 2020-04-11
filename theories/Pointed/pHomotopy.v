Require Import Basics.
Require Import Types.
Require Import Pointed.Core.
Require Import WildCat.

Local Open Scope pointed_scope.

(** Some higher homotopies *)

Definition phomotopy_inverse_1 {A : pType} {P : pFam A} {f : pForall A P}
  : (phomotopy_refl f) ^* ==* phomotopy_refl f.
Proof.
  srapply Build_pHomotopy.
  + reflexivity.
  + pointed_reduce. reflexivity.
Defined.

<<<<<<< HEAD
(** [phomotopy_path] sends concatenation to composition of pointed homotopies.*)
Definition phomotopy_path_pp `{Funext} {A : pType} {P : pFam A}
  {f g h : pForall A P} (p : f = g) (q : g = h)
  : phomotopy_path (p @ q) ==* phomotopy_path p @* phomotopy_path q.
Proof.
  induction p. induction q. symmetry. apply phomotopy_compose_p1.
Defined.
=======
(** ** Whiskering of pointed homotopies by pointed functions *)

Definition pmap_postwhisker {A B C : pType} {f g : A ->* B}
  (h : B ->* C) (p : f ==* g) : h o* f ==* h o* g.
Proof.
  pointed_reduce'.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros a; apply ap, p.
  - apply whiskerR.
    apply ap.
    symmetry.
    apply concat_p1.
Defined.

Definition pmap_prewhisker {A B C : pType} (f : A ->* B)
  {g h : B ->* C} (p : g ==* h) : g o* f ==* h o* f.
Proof.
  pointed_reduce'.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros a; apply p.
  - symmetry; apply concat_1p.
Defined.

(** ** Composition of pointed homotopies *)
>>>>>>> master

Definition phomotopy_path2 `{Funext} {A : pType} {P : pFam A}
  {f g : pForall A P} {p p' : f = g} (q : p = p')
  : phomotopy_path p ==* phomotopy_path p'.
Proof.
<<<<<<< HEAD
  induction q. reflexivity.
Defined.
=======
  simple refine (Build_pHomotopy _ _); cbn.
  - intros x; exact ((pointed_htpy p) x @ (pointed_htpy q) x).
  - simpl.
    refine (concat_pp_p _ _ _ @ _).
    refine (whiskerL _ (point_htpy q) @ _).
    exact (point_htpy p).
Defined.

Infix "@*" := phomotopy_compose : pointed_scope.

(* pointed homotopy is a transitive relation *)
Global Instance phomotopy_transitive {A B} : Transitive (@pHomotopy A B)
  := @phomotopy_compose A B.
>>>>>>> master

(** [phomotopy_path] sends inverses to inverses.*)
Definition phomotopy_path_V `{Funext} {A : pType} {P : pFam A}
  {f g : pForall A P} (p : f = g)
  : phomotopy_path (p^) ==* (phomotopy_path p)^*.
Proof.
<<<<<<< HEAD
  induction p. simpl. symmetry. apply phomotopy_inverse_1.
Defined.
=======
  intros p; pointed_reduce'.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros x; exact ((p x)^).
  - apply concat_V_pp.
Defined.

(* pointed homotopy is a symmetric relation *)
Global Instance phomotopy_symmetric {A B} : Symmetric (@pHomotopy A B)
  := @phomotopy_inverse A B.


Notation "p ^*" := (phomotopy_inverse p) : pointed_scope.
>>>>>>> master

Definition phomotopy_hcompose `{Funext} {A : pType} {P : pFam A} {f g h : pForall A P}
 {p p' : f ==* g} {q q' : g ==* h} (r : p ==* p') (s : q ==* q') :
  p @* q ==* p' @* q'.
Proof.
  exact ((s $@R p) $@ (q' $@L r)).
Defined.

Reserved Infix "@@*" (at level 30).
Notation "p @@* q" := (phomotopy_hcompose p q).

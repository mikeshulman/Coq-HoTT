Require Import Basics.
Require Import Types.
Require Import Pointed.Core.

Local Open Scope pointed_scope.

(* pointed homotopy is a reflexive relation *)
Global Instance phomotopy_reflexive {A} {P : pFam A} 
  : Reflexive (@pHomotopy A P).
Proof.
  intro.
  serapply Build_pHomotopy'.
  + intro. reflexivity.
  + exact ((concat_pV _)^).
Defined.

(** ** Whiskering of pointed homotopies by pointed functions *)

Definition pmap_postwhisker {A B C : pType} {f g : A ->* B}
  (h : B ->* C) (p : f ==* g) : h o* f ==* h o* g.
Proof.
  srefine (Build_pHomotopy _ _); cbn.
  - exact (fun x => ap h (p x)).
  - abstract (pointed_reduce; reflexivity).
Defined.

Definition pmap_prewhisker {A B C : pType} (f : A ->* B)
  {g h : B ->* C} (p : g ==* h) : g o* f ==* h o* f.
Proof.
  srefine (Build_pHomotopy _ _); cbn.
  - exact (fun x => p (f x)).
  - abstract (pointed_reduce; reflexivity).
Defined.

(** ** Composition of pointed homotopies *)

Definition phomotopy_compose {A : pType} {P : pFam A} {f g h : pForall A P}
  (p : f ==* g) (q : g ==* h) : f ==* h.
Proof.
  srefine (Build_pHomotopy' (fun x => p x @ q x) _); cbn.
  abstract (pointed_reduce; reflexivity).
Defined.

Infix "@*" := phomotopy_compose : pointed_scope.

(* pointed homotopy is a transitive relation *)
Global Instance phomotopy_transitive {A B} : Transitive (@pHomotopy A B)
  := @phomotopy_compose A B.

Definition phomotopy_inverse {A : pType} {P : pFam A} {f g : pForall A P}
: (f ==* g) -> (g ==* f).
Proof.
  intros p; srefine (Build_pHomotopy' _ _); cbn.
  - intros x; exact ((p x)^).
  - abstract (pointed_reduce; reflexivity).
Defined.

(* pointed homotopy is a symmetric relation *)
Global Instance phomotopy_symmetric {A B} : Symmetric (@pHomotopy A B)
  := @phomotopy_inverse A B.


Notation "p ^*" := (phomotopy_inverse p) : pointed_scope.

Definition issig_phomotopy {A B : pType} (f g : A ->* B)
: { p : f == g & p (point A) = point_eq f @ (point_eq g)^ } <~> (f ==* g).
Proof.
  issig.
Defined.

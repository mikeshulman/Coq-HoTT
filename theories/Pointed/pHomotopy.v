Require Import Basics.
Require Import Types.
Require Import Pointed.Core.

Local Open Scope pointed_scope.

(* pointed homotopy is a reflexive relation *)
Global Instance phomotopy_reflexive {A} {P : pFam A} 
  : Reflexive (@pHomotopy A P).
Proof.
  intro.
  serapply Build_pHomotopy.
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
  srefine (Build_pHomotopy (fun x => p x @ q x) _); cbn.
  refine (dpoint_eq p @@ dpoint_eq q @ concat_pp_p _ _ _ @ _).
  apply whiskerL. apply concat_V_pp.
Defined.

Infix "@*" := phomotopy_compose : pointed_scope.

(* pointed homotopy is a transitive relation *)
Global Instance phomotopy_transitive {A B} : Transitive (@pHomotopy A B)
  := @phomotopy_compose A B.

Definition phomotopy_inverse {A : pType} {P : pFam A} {f g : pForall A P}
: (f ==* g) -> (g ==* f).
Proof.
  intros p; srefine (Build_pHomotopy _ _); cbn.
  - intros x; exact ((p x)^).
  - refine (inverse2 (dpoint_eq p) @ inv_pV _ _).
Defined.

(* pointed homotopy is a symmetric relation *)
Global Instance phomotopy_symmetric {A B} : Symmetric (@pHomotopy A B)
  := @phomotopy_inverse A B.


Notation "p ^*" := (phomotopy_inverse p) : pointed_scope.

Definition issig_phomotopy {A : pType} {P : pFam A} (f g : pForall A P)
: { p : f == g & p (point A) = dpoint_eq f @ (dpoint_eq g)^ } <~> (f ==* g).
Proof.
  issig.
Defined.

(** Some higher homotopies *)

Definition phomotopy_compose_h1 {A : pType} {P : pFam A} {f g : pForall A P}
 (p : f ==* g) : p @* reflexivity g ==* p.
Proof.
  serapply Build_pHomotopy.
  + intro x. apply concat_p1.
  + pointed_reduce. 
    rewrite (concat_pp_V H (concat_p1 _))^. generalize (H @ concat_p1 _). 
    clear H. intros H. destruct H.
    generalize (p ispointed_type). generalize (g ispointed_type).
    intros x q. destruct q. reflexivity.
Defined.

Definition phomotopy_compose_1h {A : pType} {P : pFam A} {f g : pForall A P}
 (p : f ==* g) : reflexivity f @* p ==* p.
Proof.
  serapply Build_pHomotopy.
  + intro x. apply concat_1p.
  + pointed_reduce. 
    rewrite (concat_pp_V H (concat_p1 _))^. generalize (H @ concat_p1 _). 
    clear H. intros H. destruct H.
    generalize (p ispointed_type). generalize (g ispointed_type).
    intros x q. destruct q. reflexivity.
Defined.

Definition phomotopy_inverse_1 {A : pType} {P : pFam A} {f : pForall A P}
  : (phomotopy_reflexive f) ^* ==* phomotopy_reflexive f.
Proof.
  serapply Build_pHomotopy.
  + reflexivity.
  + pointed_reduce. reflexivity.
Defined.
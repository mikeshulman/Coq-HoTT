(* -*- mode: coq; mode: visual-line -*- *)
Require Import Basics.
Require Import Types.

Declare Scope pointed_scope.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

Generalizable Variables A B f.

(** * Pointed Types *)

(* Pointed version of unit type *)
Global Instance ispointed_unit : IsPointed Unit := tt.

Definition pUnit : pType := (Build_pType Unit _).

(** A sigma type of pointed components is pointed. *)
Global Instance ispointed_sigma `{IsPointed A} `{IsPointed (B (point A))}
: IsPointed (sigT B)
  := (point A; point (B (point A))).

(** A cartesian product of pointed types is pointed. *)
Global Instance ispointed_prod `{IsPointed A, IsPointed B} : IsPointed (A * B)
  := (point A, point B).

(* Product of pTypes is a pType *)
Notation "X * Y" := (Build_pType (X * Y) ispointed_prod) : pointed_scope.

(* Pointed type family *)
Definition pFam (A : pType) := {P : A -> Type & P (point A)}.
Definition pfam_pr1 {A : pType} (P : pFam A) : A -> Type := pr1 P.
Coercion pfam_pr1 : pFam >-> Funclass.
Definition dpoint {A : pType} (P : pFam A) : P (point A) := pr2 P.

Definition constant_pfam {A : pType} (B : pType) : pFam A := 
  (fun _ => pointed_type B; point B).

(* IsTrunc for a pointed type family *)
Class IsTrunc_pFam n {A} (X : pFam A)
  := trunc_pfam_is_trunc : forall x, IsTrunc n (X.1 x).

(** ** Pointed dependent functions *)
Record pForall (A : pType) (P : pFam A) :=
  { pointed_fun : forall x, P x ;
    dpoint_eq : pointed_fun (point A) = dpoint P }.

Arguments dpoint_eq {A P} f : rename.
Arguments pointed_fun {A P} f : rename.
Coercion pointed_fun : pForall >-> Funclass.

(** ** Pointed functions *)

(* A pointed map is a map with a proof that it preserves the point.
  We define it as a non-dependent version of [pForall]. *)
Definition pMap (A B : pType) := pForall A (constant_pfam B).

Infix "->*" := pMap : pointed_scope.

Definition Build_pMap (A B : pType) (f : A -> B) (p : f (point A) = point B)
  : A ->* B.
Proof.
  serapply Build_pForall. 1: exact f. exact p.
Defined.

Definition point_eq {A B : pType} (f : A ->* B) : f (point A) = point B :=
  dpoint_eq f.

Definition pmap_idmap {A : pType} : A ->* A
  := Build_pMap A A idmap 1.

Definition pmap_compose {A B C : pType}
           (g : B ->* C) (f : A ->* B)
: A ->* C
  := Build_pMap A C (g o f)
                (ap g (point_eq f) @ point_eq g).

Infix "o*" := pmap_compose : pointed_scope.

(** ** Pointed homotopies *)

Definition phomotopy_fam {A : pType} {P : pFam A} (f g : pForall A P) : pFam A 
  := (fun x => f x = g x; dpoint_eq f @ (dpoint_eq g)^).

(* A pointed homotopy is a homotopy with a proof that the presevation
   paths agree.
   We define it instead as a special case of a [pForall]. This means that we can
   define pointed homotopies between pointed homotopies. *)
Definition pHomotopy {A : pType} {P : pFam A} (f g : pForall A P) : Type :=
  pForall A (phomotopy_fam f g).

Infix "==*" := pHomotopy : pointed_scope.

Definition Build_pHomotopy {A : pType} {P : pFam A} {f g : pForall A P}
  (p : f == g) (q : p (point A) = dpoint_eq f @ (dpoint_eq g)^) : f ==* g.
Proof.
  serapply Build_pForall;[exact p | exact q].
Defined.

Coercion pointed_htpy {A : pType} {P : pFam A} {f g : pForall A P}
  (h : f ==* g) : f == g :=
  h.

Definition point_htpy {A : pType} {P : pFam A} {f g : pForall A P}
  (h : f ==* g) : h (point A) @ dpoint_eq g = dpoint_eq f.
Proof.
  apply moveR_pM. exact (dpoint_eq h).
Defined.

Definition pointed_htpy' {A B} (f g : A ->* B) (p : pHomotopy f g)
  : forall x:A, f x = g x
  := fun x => pointed_htpy p x.

(* Coercion pointed_htpy' : pHomotopy >-> Funclass. *)


(** ** Pointed equivalences *)

(* A pointed equivalence is a pointed map and a proof that it is
  an equivalence *)
Record pEquiv (A B : pType) :=
  { pointed_equiv_fun : pForall A (constant_pfam B) ;
    pointed_isequiv : IsEquiv pointed_equiv_fun
  }.

(* TODO:
  It might be better behaved to define pEquiv as an equivalence and a proof that
  this equivalence is pointed.
    In pEquiv.v we have another constructor Build_pEquiv' which coq can
  infer faster than Build_pEquiv.
  *)

Infix "<~>*" := pEquiv : pointed_scope.

(* Note: because we define pMap as a special case of pForall, we must declare
  all coercions into pForall, *not* into pMap. *)
Coercion pointed_equiv_fun : pEquiv >-> pForall.
Global Existing Instance pointed_isequiv.

Coercion pointed_equiv_equiv {A B} (f : A <~>* B)
  : A <~> B := Build_Equiv A B f _.

(* Pointed sigma *)
Definition psigma {A : pType} (P : pFam A) : pType.
Proof.
  exists {x : A & P x}.
  exact (point A; P.2).
Defined.

(* Pointed pi types, note that the domain is not pointed *)
Definition pproduct {A : Type} (F : A -> pType) : pType
  := Build_pType (forall (a : A), pointed_type (F a)) (ispointed_type o F).

(** The following tactic often allows us to "pretend" that pointed maps and homotopies preserve basepoints strictly.  We have carefully defined [pMap] and [pHomotopy] so that when destructed, their second components are paths with right endpoints free, to which we can apply Paulin-Morhing path-induction. *)
Ltac pointed_reduce :=
  unfold pointed_fun, pointed_htpy; cbn;
  repeat match goal with
           | [ X : pType |- _ ] => destruct X as [X ?]
           | [ phi : pMap ?X ?Y |- _ ] => destruct phi as [phi ?]
           | [ phi : pForall ?X ?Y |- _ ] => destruct phi as [phi ?]
           | [ alpha : pHomotopy ?f ?g |- _ ] => let H := fresh in destruct alpha as [alpha H]; apply moveR_pM in H
           | [ equiv : pEquiv ?X ?Y |- _ ] => destruct equiv as [equiv ?]
         end;
  cbn in *; unfold point in *;
  path_induction; cbn;
  (** TODO: [pointed_reduce] uses [rewrite], and thus according to our current general rules, it should only be used in opaque proofs.  We don't yet need any of the proofs that use it to be transparent, but there's a good chance we will eventually.  At that point we can consider whether to allow it in transparent proofs, modify it to not use [rewrite], or exclude it from proofs that need to be transparent. *)
  rewrite ?concat_p1, ?concat_1p.

(** ** Equivalences *)

Definition issig_ptype : { X : Type & X } <~> pType.
Proof.
  issig.
Defined.

Definition issig_pmap (A B : pType)
: { f : A -> B & f (point A) = point B } <~> (A ->* B).
Proof.
  issig.
Defined.
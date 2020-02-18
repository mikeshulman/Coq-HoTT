(* -*- mode: coq; mode: visual-line -*- *)
Require Import Basics PathAny FunextVarieties UnivalenceImpliesFunext.
Require Import Types.
Require Import WildCat.

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
  unfold pointed_fun, pointed_htpy; cbn in *;
  repeat match goal with
           | [ X : pType |- _ ] => destruct X as [X ?]
           | [ P : pFam ?X |- _ ] => destruct P as [P ?]
           | [ phi : pMap ?X ?Y |- _ ] => destruct phi as [phi ?]
           | [ phi : pForall ?X ?Y |- _ ] => destruct phi as [phi ?]
           | [ alpha : pHomotopy ?f ?g |- _ ] => let H := fresh in destruct alpha as [alpha H]; try (apply moveR_pM in H)
           | [ equiv : pEquiv ?X ?Y |- _ ] => destruct equiv as [equiv ?]
         end;
  cbn in *; unfold point in *;
  path_induction; cbn;
  (** TODO: [pointed_reduce] uses [rewrite], and thus according to our current general rules, it should only be used in opaque proofs.  We don't yet need any of the proofs that use it to be transparent, but there's a good chance we will eventually.  At that point we can consider whether to allow it in transparent proofs, modify it to not use [rewrite], or exclude it from proofs that need to be transparent. *)
  rewrite ?concat_p1, ?concat_1p.

(** ** Equivalences to sigma-types. *)

Definition issig_ptype : { X : Type & X } <~> pType.
Proof.
  issig.
Defined.

Definition issig_pforall (A : pType) (P : pFam A)
: { f : forall x, P x & f (point A) = dpoint P } <~> (pForall A P).
Proof.
  issig.
Defined.

Definition issig_pmap (A B : pType)
: { f : A -> B & f (point A) = point B } <~> (A ->* B).
Proof.
  issig.
Defined.

Definition issig_phomotopy {A : pType} {P : pFam A} (f g : pForall A P)
: { p : f == g & p (point A) = dpoint_eq f @ (dpoint_eq g)^ } <~> (f ==* g).
Proof.
  issig.
Defined.

Definition issig_pequiv (A B : pType)
  : { f : A ->* B & IsEquiv f } <~> (A <~>* B).
Proof.
  issig.
Defined.

(* The record for pointed equivalences is equivalently a different sigma type *)
Definition issig_pequiv' (A B : pType)
  : { f : A <~> B & f (point A) = point B } <~> (A <~>* B).
Proof.
  transitivity { f : A ->* B & IsEquiv f }.
  2: issig.
  refine ((equiv_functor_sigma' (P := fun f => IsEquiv f.1)
    (issig_pmap A B) (fun f => equiv_idmap _)) oE _).
  refine (_ oE (equiv_functor_sigma' (Q := fun f => f.1 (point A) = point B)
    (issig_equiv A B)^-1 (fun f => equiv_idmap _))).
  refine (_ oE (equiv_sigma_assoc _ _)^-1).
  refine (equiv_sigma_assoc _ _ oE _).
  refine (equiv_functor_sigma' 1 _).
  intro; cbn; apply equiv_sigma_symm0.
Defined.

(** Various operations with pointed homotopies *)

Definition phomotopy_refl {A : pType} {P : pFam A} (f : pForall A P) : f ==* f
  := Build_pHomotopy (fun x => 1) (concat_pV _)^.

(* pointed homotopy is a reflexive relation *)
Global Instance phomotopy_reflexive {A} {P : pFam A} 
  : Reflexive (@pHomotopy A P).
Proof.
  exact phomotopy_refl.
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

(** ** Whiskering of pointed homotopies by pointed functions *)

Definition pmap_postwhisker {A B C : pType} {f g : A ->* B}
  (h : B ->* C) (p : f ==* g) : h o* f ==* h o* g.
Proof.
  srefine (Build_pHomotopy _ _); cbn.
  - exact (fun x => ap h (p x)).
  - refine (_ @ (whiskerL _ (inv_pp _ _) @ concat_pp_p _ _ _ @ whiskerL _ (concat_p_Vp _ _))^).
    exact (ap _ (dpoint_eq p) @ ap_pp _ _ _ @ whiskerL _ (ap_V _ _)).
Defined.

Definition pmap_prewhisker {A B C : pType} (f : A ->* B)
  {g h : B ->* C} (p : g ==* h) : g o* f ==* h o* f.
Proof.
  srefine (Build_pHomotopy _ _); cbn.
  - exact (fun x => p (f x)).
  - apply moveL_pV. refine (concat_p_pp _ _ _ @ whiskerR (concat_Ap p (point_eq f))^ _ @ _). 
    exact (concat_pp_p _ _ _ @ whiskerL _ (point_htpy p)).
Defined.

(** ** 1-categorical properties of [pType]. *)

Definition pmap_compose_assoc {A B C D : pType} (h : C ->* D)
  (g : B ->* C) (f : A ->* B) : (h o* g) o* f ==* h o* (g o* f).
Proof.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros ?; reflexivity.
  - abstract (pointed_reduce; reflexivity).
Defined.

Definition pmap_precompose_idmap {A B : pType} (f : A ->* B)
: f o* pmap_idmap ==* f.
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros ?; reflexivity.
  - reflexivity.
Qed.

Definition pmap_postcompose_idmap {A B : pType} (f : A ->* B)
: pmap_idmap o* f ==* f.
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _); cbn.
  - intros ?; reflexivity.
  - reflexivity.
Qed.

(** Function extensionality for pointed types and direct consequences. *)

(* By function extensionality pointed homotopies are equivalent to paths *)
Definition equiv_path_pforall `{Funext} {A : pType} {P : pFam A} (f g : pForall A P)
  : (f ==* g) <~> (f = g).
Proof.
  refine (_ oE (issig_phomotopy f g)^-1).
  revert f g; apply (equiv_path_issig_contr (issig_pforall A P)).
  { intros [f feq]; cbn.
    exists (fun a => 1%path).
    exact (concat_pV _)^. }
  intros [f feq]; cbn.
  contr_sigsig f (fun a:A => idpath (f a)); cbn.
  refine (contr_equiv' {feq' : f (point A) = dpoint P & feq = feq'} _).
  refine (equiv_functor_sigma' (equiv_idmap _) _); intros p.
  refine (_^-1 oE equiv_path_inverse _ _).
  apply equiv_moveR_1M.
Defined.

Definition path_pforall `{Funext} {A : pType} {P : pFam A} {f g : pForall A P}
  : (f ==* g) -> (f = g) := equiv_path_pforall f g.

Definition phomotopy_path `{Funext} {A : pType} {P : pFam A} {f g : pForall A P}
  : (f = g) -> (f ==* g) := (equiv_path_pforall f g)^-1 % equiv.

Definition phomotopy_path_path_pforall `{Funext} {A : pType} {P : pFam A} 
  {f g : pForall A P} (p : f ==* g)
  : phomotopy_path (path_pforall p) ==* p 
  := phomotopy_path (eissect (equiv_path_pforall f g) p).

Definition path_pforall_phomotopy_path `{Funext} {A : pType} {P : pFam A} 
  {f g : pForall A P} (p : f = g)
  : path_pforall (phomotopy_path p) = p 
  := eisretr (equiv_path_pforall f g) p.

Definition equiv_path_pmap `{Funext} {A B : pType} (f g : A ->* B)
  : (f ==* g) <~> (f = g) := equiv_path_pforall f g.

Definition path_pmap `{Funext} {A B : pType} {f g : A ->* B}
  : (f ==* g) -> (f = g) := equiv_path_pmap f g.

(* We note that the inverse of [path_pmap] computes definitionally on reflexivity, and hence [path_pmap] itself computes typally so.  *)
Definition equiv_inverse_path_pforall_1 `{Funext} {A : pType} {P : pFam A} (f : pForall A P)
  : (equiv_path_pforall f f)^-1%equiv 1%path = reflexivity f
  := 1.

Definition path_pforall_1 `{Funext} {A} {P : pFam A} {f : pForall A P}
  : path_pforall (reflexivity f) = 1%path.
Proof.
  apply moveR_equiv_M.
  reflexivity.
Defined.

Definition equiv_path_pmap_1 `{Funext} {A B} {f : A ->* B}
  : path_pforall (reflexivity f) = 1%path
  := path_pforall_1.

(** Since pointed homotopies are equivalent to equalities, we can act as if
  they are paths and define a path induction for them *)
Definition phomotopy_ind `{H0 : Funext} {A : pType} {P : pFam A}
  {k : pForall A P} (Q : forall (k' : pForall A P), (k ==* k') -> Type)
  (q : Q k (reflexivity k)) (k' : pForall A P)
  : forall (H : k ==* k'), Q k' H.
Proof.
  equiv_intro (equiv_path_pforall k k')^-1 % equiv p. induction p.
  exact q.
Defined.

(** Sometimes you have a goal with both a pointed homotopy [H] and [path_pforall H].
  This is an induction principle that allows us to replace both of them by reflexivity
  at the same time. *)
Definition phomotopy_ind' `{H0 : Funext} {A : pType} {P : pFam A}
  {k : pForall A P} (Q : forall (k' : pForall A P), (k ==* k') -> (k = k') -> Type)
  (q : Q k (reflexivity k) 1 % path) (k' : pForall A P) (H : k ==* k')
  (p : k = k') (r : path_pforall H = p)
  : Q k' H p.
Proof.
  induction r.
  revert k' H. refine (phomotopy_ind _ _).
  exact (transport (Q _ (reflexivity _)) path_pforall_1^ q).
Defined.

Definition phomotopy_ind_1 `{H0 : Funext} {A : pType} {P : pFam A}
  {k : pForall A P} (Q : forall (k' : pForall A P), (k ==* k') -> Type)
  (q : Q k (reflexivity k)) :
  phomotopy_ind Q q k (reflexivity k) = q.
Proof.
  change (reflexivity k) with ((equiv_path_pforall k k)^-1 % equiv (idpath k)).
  apply equiv_ind_comp.
Defined.

Definition phomotopy_ind_1' `{H0 : Funext} {A : pType} {P : pFam A}
  {k : pForall A P} (Q : forall (k' : pForall A P), (k ==* k') -> (k = k') -> Type)
  (q : Q k (reflexivity k) 1 % path)
  : phomotopy_ind' Q q k (reflexivity k) (path_pforall (reflexivity k)) (1 % path)
  = transport (Q k (reflexivity k)) path_pforall_1^ q.
Proof.
  serapply phomotopy_ind_1.
Defined.

(** Operations on equivalences needed to make pType a wild category with equivalences *)

(* This inverse equivalence of a pointed equivalence is again
   a pointed equivalence *)
Definition pequiv_inverse {A B} (f : A <~>* B) : B <~>* A.
Proof.
  serapply Build_pEquiv.
  1: apply (Build_pMap _ _ f^-1).
  1: apply moveR_equiv_V; symmetry; apply point_eq.
  exact _.
Defined.

(* A pointed version of Sect (sometimes useful for proofs of some equivalences) *)
Definition pSect {A B : pType} (s : A ->* B) (r : B ->* A) : Type
  := r o* s ==* pmap_idmap.

Arguments pSect _ _ / _ _.

(* A pointed equivalence is a section of its inverse *)
Definition peissect {A B : pType} (f : A <~>* B) : pSect f (pequiv_inverse f).
Proof.
  pointed_reduce.
  srefine (Build_pHomotopy _ _).
  1: apply (eissect f).
  pointed_reduce.
  unfold moveR_equiv_V.
  apply inverse, concat_1p.
Qed.

(* A pointed equivalence is a retraction of its inverse *)
Definition peisretr {A B : pType} (f : A <~>* B) : pSect (pequiv_inverse f) f.
Proof.
  srefine (Build_pHomotopy _ _).
  1: apply (eisretr f).
  pointed_reduce.
  unfold moveR_equiv_V.
  hott_simpl.
  apply eisadj.
Qed.

(** Univalence for pointed types *)
Definition equiv_path_ptype `{Univalence} (A B : pType) : A <~>* B <~> A = B.
Proof.
  destruct A as [A a], B as [B b].
  refine (equiv_ap issig_ptype (A;a) (B;b) oE _).
  refine (equiv_path_sigma _ _ _ oE _).
  refine (_ oE (issig_pequiv' _ _)^-1); simpl.
  refine (equiv_functor_sigma' (equiv_path_universe A B) _); intros f.
  apply equiv_concat_l.
  apply transport_path_universe.
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

(** Pointed types of pointed maps *)

(** A family of pointed types gives rise to a [pFam]. *)
Definition pointed_fam {A : pType} (B : A -> pType) : pFam A
  := (pointed_type o B; point (B (point A))).

(** The section of a family of pointed types *)
Definition point_pforall {A : pType} (B : A -> pType) : pForall A (pointed_fam B)
  := Build_pForall A (pointed_fam B) (fun x => point (B x)) 1.

(** The constant (zero) map *)
Definition pConst {A B : pType} : A ->* B
  := point_pforall (fun _ => B).

(** The pointed type of pointed maps. For dependent pointed maps we need
  a family of pointed types, not just a family of types with a point over the
  basepoint of [A].*)
Definition ppForall (A : pType) (B : A -> pType) : pType
  := Build_pType (pForall A (pointed_fam B)) (point_pforall B).

Definition ppMap (A B : pType) : pType
  := ppForall A (fun _ => B).

Infix "->**" := ppMap : pointed_scope.
Notation "'ppforall'  x .. y , P" := (ppForall _ (fun x => .. (ppForall _ (fun y => P)) ..))
  (at level 200, x binder, y binder, right associativity).

(** 1-categorical properties of [pForall]. We prove some results using function
  extensionality for simplicity. *)

Definition phomotopy_postwhisker `{Funext} {A : pType} {P : pFam A} {f g h : pForall A P}
  {p p' : f ==* g} (r : p ==* p') (q : g ==* h) :
  p @* q ==* p' @* q.
Proof.
  serapply Build_pHomotopy.
  + intro x. exact (whiskerR (r x) (q x)).
  + revert p' r. serapply phomotopy_ind.
    revert h q.  serapply phomotopy_ind.
    revert g p.  serapply phomotopy_ind.
    pointed_reduce. reflexivity.
Defined.

Definition phomotopy_prewhisker `{Funext} {A : pType} {P : pFam A} {f g h : pForall A P}
  (p : f ==* g) {q q' : g ==* h} (s : q ==* q') :
  p @* q ==* p @* q'.
Proof.
  serapply Build_pHomotopy.
  + intro x. exact (whiskerL (p x) (s x)).
  + revert q' s. serapply phomotopy_ind.
    revert h q.  serapply phomotopy_ind.
    revert g p.  serapply phomotopy_ind.
    pointed_reduce. reflexivity.
Defined.

Definition phomotopy_compose_assoc `{Funext} {A : pType} {P : pFam A} 
  {f g h k : pForall A P}
  (p : f ==* g) (q : g ==* h) (r : h ==* k) : p @* (q @* r) ==* (p @* q) @* r.
Proof.
  serapply Build_pHomotopy.
  + intro x. exact (concat_p_pp (p x) (q x) (r x)).
  + revert k r. serapply phomotopy_ind.
    revert h q. serapply phomotopy_ind.
    revert g p. serapply phomotopy_ind.
    pointed_reduce. reflexivity.
Defined.

Definition phomotopy_compose_p1 {A : pType} {P : pFam A} {f g : pForall A P}
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

Definition phomotopy_compose_1p {A : pType} {P : pFam A} {f g : pForall A P}
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

Definition phomotopy_compose_pV `{Funext} {A : pType} {P : pFam A} {f g : pForall A P}
 (p : f ==* g) : p @* p ^* ==* phomotopy_refl f.
Proof.
  serapply Build_pHomotopy.
  + intro x. apply concat_pV.
  + revert g p. serapply phomotopy_ind. 
    pointed_reduce. reflexivity.
Defined.

Definition phomotopy_compose_Vp `{Funext} {A : pType} {P : pFam A} {f g : pForall A P}
 (p : f ==* g) : p ^* @* p ==* phomotopy_refl g.
Proof.
  serapply Build_pHomotopy.
  + intro x. apply concat_Vp.
  + revert g p. serapply phomotopy_ind. 
    pointed_reduce. reflexivity.
Defined.

(** * pType as a wild category *)

Global Instance isgraph_ptype : IsGraph pType
  := Build_IsGraph pType pMap.

Global Instance is01cat_ptype : Is01Cat pType
  := Build_Is01Cat pType _ (@pmap_idmap) (@pmap_compose).

Global Instance isgraph_pforall (A : pType) (P : pFam A) : IsGraph (pForall A P)
  := Build_IsGraph _ pHomotopy.

Global Instance is01cat_pforall (A : pType) (P : pFam A) : Is01Cat (pForall A P).
Proof.
  econstructor.
  - exact phomotopy_refl.
  - intros a b c f g. exact (phomotopy_compose g f).
Defined.

Global Instance is0gpd_pforall (A : pType) (P : pFam A) : Is0Gpd (pForall A P).
Proof.
  srapply Build_Is0Gpd. intros ? ? h. exact (phomotopy_inverse h).
Defined.

Global Instance is1cat_ptype : Is1Cat pType.
Proof.
  econstructor.
  - intros A B C h; rapply Build_Is0Functor.
    intros f g p; cbn.
    apply pmap_postwhisker; assumption.
  - intros A B C h; rapply Build_Is0Functor.
    intros f g p; cbn.
    apply pmap_prewhisker; assumption.
  - intros ? ? ? ? f g h; exact (pmap_compose_assoc h g f).
  - intros ? ? f; exact (pmap_postcompose_idmap f).
  - intros ? ? f; exact (pmap_precompose_idmap f).
Defined.

Global Instance hasmorext_ptype `{Funext} : HasMorExt pType.
Proof.
  srapply Build_HasMorExt; intros A B f g.
  refine (isequiv_homotopic (equiv_path_pmap f g)^-1 % equiv _).
  intros []; reflexivity.
Defined.

Global Instance hasequivs_ptype : HasEquivs pType.
Proof.
  srapply (Build_HasEquivs _ _ _ _ pEquiv (fun A B f => IsEquiv f));
    intros A B f; cbn; intros.
  - exact f.
  - exact _.
  - exact (Build_pEquiv _ _ f _).
  - reflexivity.
  - exact (pequiv_inverse f).
  - apply peissect.
  - cbn. refine (peisretr f).
  - rapply (isequiv_adjointify f g).
    + intros x; exact (r x).
    + intros x; exact (s x).
Defined.

Global Instance isunivalent_ptype `{Univalence} : IsUnivalent1Cat pType.
Proof.
  srapply Build_IsUnivalent1Cat; intros A B.
  refine (isequiv_homotopic (equiv_path_ptype A B)^-1 % equiv _).
  intros []; apply path_pequiv.
  srefine (Build_pHomotopy _ _).
  - intros x; reflexivity.
  - (* Some messy path algebra here. *)
Abort.

Global Instance ispointedcat_ptype : IsPointedCat pType.
Proof.
  serapply Build_IsPointedCat.
  + exact pUnit.
  + intro A.
    exists pConst.
    intro f.
    serapply Build_pHomotopy.
    - intros [].
      exact (point_eq _).
    - symmetry; cbn.
      apply concat_p1.
  + intro B.
    exists pConst.
    intro f.
    serapply Build_pHomotopy.
    - intros b.
      apply path_unit.
    - serapply path_contr.
Defined.

Definition path_zero_morphism_pconst (A B : pType)
  : (@pConst A B) = zero_morphism := idpath.

Global Instance is1cat_pforall `{Funext} (A : pType) (P : pFam A) : Is1Cat (pForall A P).
Proof.
  econstructor.
  - intros f g h p; rapply Build_Is0Functor.
    intros q r s. exact (phomotopy_postwhisker s p).
  - intros f g h p; rapply Build_Is0Functor.
    intros q r s. exact (phomotopy_prewhisker p s).
  - intros ? ? ? ? p q r. simpl. exact (phomotopy_compose_assoc p q r).
  - intros ? ? p; exact (phomotopy_compose_p1 p).
  - intros ? ? p; exact (phomotopy_compose_1p p).
Defined.

Global Instance is1gpd_pforall `{Funext} (A : pType) (P : pFam A) : Is1Gpd (pForall A P).
Proof.
  econstructor.
  + intros ? ? p. exact (phomotopy_compose_pV p).
  + intros ? ? p. exact (phomotopy_compose_Vp p).
Defined.

(* Global Instance is21cat_pType `{Funext} : Is21Cat pType.
Proof.
  econstructor.
  - exact _.
  - intros ? ? ? f. simpl.
Defined. *)

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


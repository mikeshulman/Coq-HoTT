Require Import Basics Types PathAny FunextVarieties.
Require Import Pointed.Core.
Require Import Pointed.pHomotopy.
Require Import WildCat.

Local Open Scope pointed_scope.

(* By function extensionality pointed homotopies are equivalent to paths *)
Definition equiv_path_pforall `{Funext} {A : pType} {P : pFam A} (f g : pForall A P)
  : (f ==* g) <~> (f = g).
Proof.
  refine (_ oE (issig_phomotopy f g)^-1).
  eqp_issig_contr (issig_pforall A P).
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

(** [phomotopy_path] sends concatenation to composition of pointed homotopies.*)
Definition phomotopy_path_pp `{Funext} {A : pType} {P : pFam A} 
  {f g h : pForall A P} (p : f = g) (q : g = h)
  : phomotopy_path (p @ q) ==* phomotopy_path p @* phomotopy_path q.
Proof.
  induction p. induction q. symmetry. apply phomotopy_compose_h1.
Defined.

(** [phomotopy_path] sends inverses to inverses.*)
Definition phomotopy_path_V `{Funext} {A : pType} {P : pFam A} 
  {f g : pForall A P} (p : f = g)
  : phomotopy_path (p^) ==* (phomotopy_path p)^*.
Proof.
  induction p. simpl. symmetry. apply phomotopy_inverse_1.
Defined.

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
  : Q k' H (path_pforall H).
Proof.
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
  : phomotopy_ind' Q q k (reflexivity k)
  = transport (Q k (reflexivity k)) path_pforall_1^ q.
Proof.
  serapply phomotopy_ind_1.
Defined.

(** ** Associativity of pointed map composition *)

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

(** ** Trivially pointed maps *)

(** Not infrequently we have a map between two unpointed types and want to consider it as a pointed map that trivially respects some given point in the domain. *)
Definition pmap_from_point {A B : Type} (f : A -> B) (a : A)
  : Build_pType A a ->* Build_pType B (f a)
  := Build_pMap (Build_pType A a) (Build_pType B (f a)) f 1%path.

(** A variant of [pmap_from_point] where the domain is pointed, but the codomain is not. *)
Definition pmap_from_pointed {A : pType} {B : Type} (f : A -> B)
  : A ->* Build_pType B (f (point A))
  := Build_pMap A (Build_pType B (f (point A))) f 1%path.

(** The same, for a dependent pointed map. *)
Definition pforall_from_pointed {A : pType} {B : A -> Type} (f : forall x, B x)
  : pForall A (B; f (point A))
  := Build_pForall A (B; (f (point A))) f 1%path.

(** A family of pointed types gives rise to a [pFam]. *)
Definition pointed_fam {A : pType} (B : A -> pType) : pFam A
  := (pointed_type o B; point (B (point A))).

(** The section of a family of pointed types *)
Definition point_pforall {A : pType} (B : A -> pType) : pForall A (pointed_fam B)
  := Build_pForall A (pointed_fam B) (fun x => point (B x)) 1.

(** The constant (zero) map *)
Definition pConst {A B : pType} : A ->* B
  := point_pforall (fun _ => B).

(* precomposing the zero map is the zero map *)
Lemma precompose_pconst {A B C : pType} (f : B ->* C)
  : f o* @pConst A B ==* pConst.
Proof.
  serapply Build_pHomotopy.
  1: intro; apply point_eq.
  exact (concat_p1 _ @ concat_1p _)^.
Defined.

(* postcomposing the zero map is the zero map *)
Lemma postcompose_pconst {A B C : pType} (f : A ->* B)
  : pConst o* f ==* @pConst A C.
Proof.
  serapply Build_pHomotopy.
  1: reflexivity.
  exact (concat_p1 _ @ concat_p1 _ @ ap_const _ _)^.
Defined.

Lemma pmap_punit_pconst {A : pType} {f : A ->* pUnit} : f ==* pConst.
Proof.
  serapply Build_pHomotopy.
  1: intro; apply path_unit.
  apply path_contr.
Defined.

Lemma pconst_factor {A B : pType} {f : pUnit ->* B} {g : A ->* pUnit}
  : f o* g ==* pConst.
Proof.
  refine (_ @* precompose_pconst f).
  apply pmap_postwhisker.
  apply pmap_punit_pconst.
Defined.

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

(** If we have a fiberwise pointed map, with a variable as codomain, this is an
  induction principle that allows us to assume it respects all basepoints by
  reflexivity*)
Definition fiberwise_pointed_map_rec `{H0 : Funext} {A : Type} {B : A -> pType}
  (P : forall (C : A -> pType) (g : forall a, B a ->* C a), Type)
  (H : forall (C : A -> Type) (g : forall a, B a -> C a),
     P _ (fun a => pmap_from_pointed (g a)))
  : forall (C : A -> pType) (g : forall a, B a ->* C a), P C g.
Proof.
  equiv_intros (equiv_functor_arrow' (equiv_idmap A) issig_ptype oE
    equiv_sigT_coind _ _) C.
  destruct C as [C c0].
  equiv_intros (@equiv_functor_forall_id _ A _ _
    (fun a => issig_pmap (B a) (Build_pType (C a) (c0 a))) oE
    equiv_sigT_coind _ _) g.
  simpl in *. destruct g as [g g0].
  unfold point in g0. unfold functor_forall, sigT_coind_uncurried. simpl.
  (* now we need to apply path induction on the homotopy g0 *)
  pose (path_forall _ c0 g0).
  assert (p = path_forall (fun x : A => g x (ispointed_type (B x))) c0 g0).
  1: reflexivity.
  induction p.
  apply moveR_equiv_V in X. induction X.
  apply H.
Defined.

(** Some higher homotopies that use [phomotopy_ind]. *)

Definition phomotopy_hcompose `{Funext} {A : pType} {P : pFam A} {f g h : pForall A P}
 {p p' : f ==* g} {q q' : g ==* h} (r : p ==* p') (s : q ==* q') : 
  p @* q ==* p' @* q'.
Proof.
  serapply Build_pHomotopy.
  + intro x. exact (r x @@ s x). 
  + revert q' s. serapply phomotopy_ind.
    revert p' r. serapply phomotopy_ind.
    revert h q.  serapply phomotopy_ind.
    revert g p.  serapply phomotopy_ind.
    pointed_reduce. reflexivity.
Defined.

Reserved Infix "@@*" (at level 30).
Notation "p @@* q" := (phomotopy_hcompose p q).

(* move? or does this already exist? *)
Definition injective_equiv {A B : Type} (f : A <~> B) {a a' : A} (p : f a = f a') 
  : a = a'.
Proof.
  exact ((eissect f a)^ @ ap (f ^-1) p @ eissect f a').
Defined.

(** A alternative constructor to build a pHomotopy between maps into pForall *)
Definition Build_pHomotopy_pForall `{Funext} {A B : pType} {C : B -> pType}
  {f g : A ->* ppforall b, C b} (p : forall a, f a ==* g a)
  (q : p (point A) ==* phomotopy_path (point_eq f) @* (phomotopy_path (point_eq g))^*) 
  : f ==* g.
Proof.
  serapply Build_pHomotopy.
  + intro a. exact (path_pforall (p a)).
  + apply ((equiv_ap (equiv_path_pforall _ _)^-1 % equiv) _ _).
    refine (eissect _ _ @ _).
    refine (path_pforall (q @* _)).
    symmetry.
    refine (phomotopy_path_pp _ _ @* _).
    refine (reflexivity _ @@* _).
    apply phomotopy_path_V.
Defined.

(** Operations on dependent pointed maps *)

(* functorial action of [pForall A B] in [B] *)
Definition functor_pforall_right {A : pType} {B B' : pFam A}
  (f : forall a, B a -> B' a)
  (p : f (point A) (dpoint B) = dpoint B') (g : pForall A B)
    : pForall A B' :=
  Build_pForall A B' (fun a => f a (g a)) (ap (f (point A)) (dpoint_eq g) @ p).

Definition functor2_pforall_right {A : pType} {B C : pFam A} 
  {g g' : forall (a : A), B a -> C a}
  {g₀ : g (point A) (dpoint B) = dpoint C} 
  {g₀' : g' (point A) (dpoint B) = dpoint C} {f f' : pForall A B}
  (p : forall a, g a == g' a) (q : f ==* f') 
  (r : p (point A) (dpoint B) @ g₀' = g₀) 
  : functor_pforall_right g g₀ f ==* functor_pforall_right g' g₀' f'.
Proof.
  serapply Build_pHomotopy.
  1: { intro a. refine (p a (f a) @ ap (g' a) (q a)). }
  pointed_reduce. symmetry. apply concat_Ap.
  (* Alternative proof using funext, possibly useful if we want to show
    that [functor2_pforall_right] applied to reflexivity is reflexivity.
  revert f' q. refine (phomotopy_ind _ _). induction r.
  destruct C as [C c0]. simpl in g', g₀'. destruct g₀'. simpl.
  refine (concat_p1 _ @ moveL_pV _ _ _ _).
  refine (whiskerL _ (concat_p1 _) @ _^ @ whiskerL _ (concat_p1 _)^).
  apply concat_Ap.
  *)
Defined.

(* functorial action of [pForall A (pointed_fam B)] in [B]. *)
Definition pmap_compose_ppforall {A : pType} {B B' : A -> pType}
  (g : forall a, B a ->* B' a) (f : ppforall a, B a) : ppforall a, B' a.
Proof.
  simple refine (functor_pforall_right _ _ f).
  + exact g.
  + exact (point_eq (g (point A))).
Defined.

Definition pmap_compose_ppforall_point {A : pType} {B B' : A -> pType}
  (g : forall a, B a ->* B' a)
  : pmap_compose_ppforall g (point_pforall B) ==* point_pforall B'.
Proof.
  serapply Build_pHomotopy.
  + intro x. exact (point_eq (g x)).
  + exact (concat_p1 _ @ concat_1p _)^.
Defined.

Definition pmap_compose_ppforall_compose {A : pType} {P Q R : A -> pType} 
  (h : forall (a : A), Q a ->* R a) (g : forall (a : A), P a ->* Q a) 
  (f : ppforall a, P a)
  : pmap_compose_ppforall (fun a => h a o* g a) f ==* pmap_compose_ppforall h (pmap_compose_ppforall g f).
Proof.
  serapply Build_pHomotopy.
  + reflexivity.
  + simpl. refine ((whiskerL _ (inverse2 _)) @ concat_pV _)^.
    refine (whiskerR _ _ @ concat_pp_p _ _ _). 
    refine (ap_pp _ _ _ @ whiskerR (ap_compose _ _ _)^ _).
Defined.

(* Definition pmap_compose_ppforall_compose_point {A : pType} {P Q R : A -> pType} 
  (g : forall a, Q a ->* R a) (f : forall a, P a ->* Q a)
  : pmap_compose_ppforall_compose g f (point_pforall P) @* _ @* _ ==* _.
 *)(*
Definition ppi_assoc_ppi_const_right (g : forall a, Q a ->* R a) (f : forall a, P a ->* Q a) :
  ppi_assoc g f (ppi_const P) @*
  (pmap_compose_ppi_phomotopy_right _ (pmap_compose_ppi_ppi_const f) @*
  pmap_compose_ppi_ppi_const g) = pmap_compose_ppi_ppi_const (fun a => g a o* f a).
Proof.
  revert R g, refine fiberwise_pointed_map_rec _ _,
  revert Q f, refine fiberwise_pointed_map_rec _ _,
  intro Q f R g,
  refine ap (fun x => _ @* (x @* _)) !pmap_compose_ppi2_refl @ _,
  reflexivity
Defined.
*)


Definition pmap_compose_ppforall2 {A : pType} {P Q : A -> pType} {g g' : forall (a : A), P a ->* Q a}
  {f f' : ppforall (a : A), P a} (p : forall a, g a ==* g' a) (q : f ==* f') 
  : pmap_compose_ppforall g f ==* pmap_compose_ppforall g' f'.
Proof.
  serapply functor2_pforall_right.
  + exact p.
  + exact q.
  + exact (point_htpy (p (point A))).
Defined.

Definition pmap_compose_ppforall2_left {A : pType} {P Q : A -> pType} {g g' : forall (a : A), P a ->* Q a}
  (f : ppforall (a : A), P a) (p : forall a, g a ==* g' a) 
  : pmap_compose_ppforall g f ==* pmap_compose_ppforall g' f :=
  pmap_compose_ppforall2 p (reflexivity f).

Definition pmap_compose_ppforall_pid_left {A : pType} {P : A -> pType}
  (f : ppforall (a : A), P a) : pmap_compose_ppforall (fun a => pmap_idmap) f ==* f.
Proof.
  serapply Build_pHomotopy.
  + reflexivity.
  + symmetry. refine (whiskerR (concat_p1 _ @ ap_idmap _) _ @ concat_pV _).
Defined.

(* functorial action of [ppForall A B] in [B]. *)
Definition functor_ppforall_right `{Funext} {A : pType} {B B' : A -> pType}
  (g : forall a, B a ->* B' a) :
  (ppforall a, B a) ->* ppforall a, B' a.
Proof.
  serapply Build_pMap.
  + serapply functor_pforall_right.
    - exact g.
    - exact (point_eq (g (point A))).
  + apply path_pforall. apply pmap_compose_ppforall_point.
Defined.

Definition functor_ppforall_right_compose `{Funext} {A : pType} {B1 B2 B3 : A -> pType}
  (g : forall a, B2 a ->* B3 a) (f : forall a, B1 a ->* B2 a)
  : functor_ppforall_right (fun a => g a o* f a) ==* 
    functor_ppforall_right g o* functor_ppforall_right f.
Proof.
  serapply Build_pHomotopy_pForall.
  + intro x. apply pmap_compose_ppforall_compose.
  + simpl. refine (_ @* (phomotopy_path_path_pforall _ @@* _)^*).
Admitted.
(*
  begin
    fapply phomotopy_mk_ppi,
    { exact ppi_assoc g f },
    { refine idp ◾** (!phomotopy_of_eq_con ⬝
        (ap phomotopy_of_eq !pmap_compose_ppi_eq_of_phomotopy ⬝ !phomotopy_of_eq_of_phomotopy) ◾**
        !phomotopy_of_eq_of_phomotopy) ⬝ _ ⬝ !phomotopy_of_eq_of_phomotopy⁻¹,
      apply ppi_assoc_ppi_const_right },
  end
*)

Definition functor2_ppforall_right `{Funext} {A : pType} {B B' : A -> pType}
  (g g' : forall a, B a ->* B' a) 
  : functor_ppforall_right g ==* functor_ppforall_right g'.
Admitted.
(*
  begin
    apply phomotopy_of_eq, apply ap pppi_compose_left, apply eq_of_homotopy, intro a,
    apply eq_of_phomotopy, exact p a
  end
*)

(* We need more boilerplate code to show that ppforall + functor_ppforall forms a functor,
   so we currently declare this property in an ad-hoc way. *)
(* Definition functor_ppforall_right_square `{Funext} {A : pType} 
  {B00 B02 B20 B22 : A -> pType} {f10 : forall a, B00 a $-> B20 a}
  {f01 : forall a, B00 a $-> B02 a} {f21 : forall a, B20 a $-> B22 a}
  {f12 : forall a, B02 a $-> B22 a} 
  (s : forall a, Square (f10 a) (f12 a) (f01 a) (f21 a))
  : Square (A := pType) (H0 := is1cat_ptype) (functor_ppforall_right f10) (functor_ppforall_right f12)
           (functor_ppforall_right f01) (functor_ppforall_right f21).
Proof.
  apply functor_ppforall_right_compose.
Defined.
 *)(*
  begin
    refine (pppi_compose_left_pcompose fright ftop)⁻¹* ⬝* _ ⬝*
           (pppi_compose_left_pcompose fbot fleft),
    exact pppi_compose_left_phomotopy psq
  end
*)
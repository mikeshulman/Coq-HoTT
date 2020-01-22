Require Import Basics Types PathAny FunextVarieties.
Require Import Pointed.Core.
Require Import Pointed.pHomotopy.
Require Import WildCat.

Local Open Scope pointed_scope.

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

(* TODO: generalize to wild categories with 0 object. *)
Definition hconst_square {A B C D : pType} {f : A $-> B} {g : C $-> D} : 
  Square pConst pConst f g :=
  precompose_pconst g $@ (postcompose_pconst f)^$.

Definition vconst_square {A B C D : pType} {f : A $-> B} {g : C $-> D} : 
  Square f g pConst pConst :=
  postcompose_pconst f $@ (precompose_pconst g)^$.

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
Defined.

Definition functor2_pforall_right_refl {A : pType} {B C : pFam A} 
  (g : forall a, B a -> C a) (g₀ : g (point A) (dpoint B) = dpoint C) 
  (f : pForall A B) 
  : functor2_pforall_right (fun a => reflexivity (g a)) (phomotopy_refl f) 
      (concat_1p _) 
    ==* phomotopy_refl (functor_pforall_right g g₀ f).
Proof.
  pointed_reduce. reflexivity.
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
  pmap_compose_ppforall2 p (phomotopy_refl f).

Definition pmap_compose_ppforall2_right {A : pType} {P Q : A -> pType} (g : forall (a : A), P a ->* Q a)
  {f f' : ppforall (a : A), P a} (q : f ==* f') 
  : pmap_compose_ppforall g f ==* pmap_compose_ppforall g f' :=
  pmap_compose_ppforall2 (fun a => phomotopy_refl (g a)) q.

Definition pmap_compose_ppforall2_refl `{Funext} {A : pType} {P Q : A -> pType} 
  (g : forall (a : A), P a ->* Q a) (f : ppforall (a : A), P a) 
  : pmap_compose_ppforall2 (fun a => phomotopy_refl (g a)) (phomotopy_refl f) 
    ==* phomotopy_refl _.
Proof.
  simpl. 
  unfold pmap_compose_ppforall2.
  revert Q g. refine (fiberwise_pointed_map_rec _ _). intros Q g.
  serapply functor2_pforall_right_refl.
Defined.

Definition pmap_compose_ppforall_pid_left {A : pType} {P : A -> pType}
  (f : ppforall (a : A), P a) : pmap_compose_ppforall (fun a => pmap_idmap) f ==* f.
Proof.
  serapply Build_pHomotopy.
  + reflexivity.
  + symmetry. refine (whiskerR (concat_p1 _ @ ap_idmap _) _ @ concat_pV _).
Defined.

Definition pmap_compose_ppforall_path_pforall `{Funext} {A : pType} {P Q : A -> pType}
  (g : forall a, P a ->* Q a) {f f' : ppforall a, P a} (p : f ==* f') :
  ap (pmap_compose_ppforall g) (path_pforall p) =
  path_pforall (pmap_compose_ppforall2_right g p).
Proof.
  revert f' p. refine (phomotopy_ind _ _).
  refine (ap _ path_pforall_1 @ path_pforall_1^ @ ap _ _^).
  exact (path_pforall (pmap_compose_ppforall2_refl _ _)).
Defined.

Definition pmap_compose_ppforall_compose_point `{Funext} {A : pType} {P Q R : A -> pType} 
  (g : forall a, Q a ->* R a) (f : forall a, P a ->* Q a)
  : Square (pmap_compose_ppforall_compose g f (point_pforall P)) 
           (pmap_compose_ppforall_point g)^* 
           (pmap_compose_ppforall_point (fun a => g a o* f a))
           (pmap_compose_ppforall2_right _ (pmap_compose_ppforall_point f)).
Proof.
  revert R g. refine (fiberwise_pointed_map_rec _ _).
  revert Q f. refine (fiberwise_pointed_map_rec _ _).
  intros Q f R g.
  refine (_ $@hR pmap_compose_ppforall2_refl _ _).
  exact (phomotopy_refl _).
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
  (g : forall a, B2 a $-> B3 a) (f : forall a, B1 a $-> B2 a)
  : functor_ppforall_right (fun a => g a o* f a) $==
    functor_ppforall_right g o* functor_ppforall_right f.
Proof.
  serapply Build_pHomotopy_pForall.
  + intro x. apply pmap_compose_ppforall_compose.
  + refine (_ $@ (phomotopy_path_path_pforall _ @@* _)^$).
    2: refine (gpd_rev2 (phomotopy_path_pp _ _ $@ 
      ((phomotopy_path2 (pmap_compose_ppforall_path_pforall _ _) @* phomotopy_path_path_pforall _) @@* 
        (phomotopy_path_path_pforall _))) $@ 
      gpd_rev_pp _ _).
    refine (_ $@ (cat_assoc _ _ _)^$).
    apply gpd_moveL_Vh.
    apply pmap_compose_ppforall_compose_point.
Defined.

Definition functor2_ppforall_right `{Funext} {A : pType} {B B' : A -> pType}
  {g g' : forall a, B a ->* B' a} (p : forall a, g a ==* g' a)
  : functor_ppforall_right g ==* functor_ppforall_right g'.
Proof.
  apply phomotopy_path. apply ap. funext a. exact (path_pforall (p a)).
Defined.

(* We need more category instances to show that ppforall + functor_ppforall forms a functor,
   so we currently declare this property in an ad-hoc way. *)
Definition functor_ppforall_right_square `{Funext} {A : pType} 
  {B00 B02 B20 B22 : A -> pType} {f10 : forall a, B00 a $-> B20 a}
  {f01 : forall a, B00 a $-> B02 a} {f21 : forall a, B20 a $-> B22 a}
  {f12 : forall a, B02 a $-> B22 a} 
  (s : forall a, Square (f10 a) (f12 a) (f01 a) (f21 a))
  : Square (A := pType) (H0 := is1cat_ptype) (functor_ppforall_right f10) (functor_ppforall_right f12)
           (functor_ppforall_right f01) (functor_ppforall_right f21).
Proof.
  refine ((functor_ppforall_right_compose _ _)^$ $@ _).
  refine (_ $@ functor_ppforall_right_compose _ _).
  exact (functor2_ppforall_right s).
Defined.

Definition equiv_ppforall_right `{Funext} {A : pType} {B B' : A -> pType}
  (g : forall a, B a $<~> B' a) :
  (ppforall a, B a) $<~> ppforall a, B' a.
Proof.
  rapply (Build_pEquiv _ _ (functor_ppforall_right g)). 
  serapply isequiv_adjointify.
  { exact (functor_ppforall_right (fun x => (g x) ^-1$)). }
  { intro f. apply path_pforall.
    refine ((pmap_compose_ppforall_compose _ _ _)^* @* _).
    refine (pmap_compose_ppforall2_left _ (fun a => peisretr _) @* _).
    apply pmap_compose_ppforall_pid_left. }
  { intro f. apply path_pforall.
    refine ((pmap_compose_ppforall_compose _ _ _)^* @* _).
    refine (pmap_compose_ppforall2_left _ (fun a => peissect _) @* _).
    apply pmap_compose_ppforall_pid_left. }
Defined.

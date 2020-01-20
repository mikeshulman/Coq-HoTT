Require Import Basics.
Require Import Types.
Require Import Fibrations.
Require Import Pointed.Core.
Require Import Pointed.pEquiv.
Require Import Pointed.Loops.

Local Open Scope pointed_scope.

(** ** Pointed fibers *)

Definition pfiber {A B : pType} (f : A ->* B) : pType.
Proof.
  refine (Build_pType (hfiber f (point B)) _); try exact _.
  exists (point A).
  apply point_eq.
Defined.

Definition pfib {A B : pType} (f : A ->* B) : pfiber f ->* A
  := (Build_pMap (pfiber f) A pr1 1).

(** The double fiber object is equivalent to loops on the base. *)
Definition pfiber2_loops {A B : pType} (f : A ->* B)
: pfiber (pfib f) <~>* loops B.
Proof.
  apply issig_pequiv'; simple refine (_;_).
  - simpl; unfold hfiber.
    refine (_ oE (equiv_sigma_assoc _ _)^-1); simpl.
    refine (_ oE (equiv_functor_sigma'
                   (P := fun a => {_ : f a = point B & a = point A})
                   (Q := fun a => {_ : a = point A & f a = point B })
                   1 (fun a => equiv_sigma_symm0 _ _))).
    refine (_ oE equiv_sigma_assoc _ (fun a => f a.1 = point B)).
    refine (_ oE equiv_contr_sigma _); simpl.
    apply equiv_concat_l.
    symmetry; apply point_eq.
  - simpl.
    apply concat_Vp.
Defined.

(** The triple-fiber functor is equal to the negative of the loopspace functor. *)
Definition pfiber2_loops_functor {A B : pType} (f : A ->* B)
: pfiber2_loops f o* pfib (pfib (pfib f))
  ==* loops_functor f o* (loops_inv _ o* pfiber2_loops (pfib f)).
Proof.
  pointed_reduce.
  simple refine (Build_pHomotopy _ _).
  - intros [[xp q] r]. simpl in *.
    rewrite !transport_paths_Fl.
    rewrite inv_pp, !ap_V, !inv_V, ap_compose, !ap_pp, inv_pp.
    simpl; rewrite !concat_1p, !concat_p1.
    rewrite ap_pr1_path_basedpaths', ap_pp.
    rewrite <- (inv_V r); set (s := r^); clearbody s; clear r; destruct s.
    reflexivity.
  - reflexivity.
Qed.

Definition pfiber_loops_functor {A B : pType} (f : A ->* B)
  : pfiber (loops_functor f) <~>* loops (pfiber f).
Proof.
  serapply Build_pEquiv'.
  { etransitivity.
    2: serapply equiv_path_sigma.
    simpl; unfold hfiber.
    serapply equiv_functor_sigma_id.
    intro p; cbn.
    refine (_ oE equiv_moveL_Mp _ _ _).
    refine (_ oE equiv_concat_r (concat_p1 _) _).
    refine (_ oE equiv_moveL_Vp _ _ _).
    refine (_ oE equiv_path_inverse _ _).
    apply equiv_concat_l.
    apply transport_paths_Fl. }
  by pointed_reduce.
Defined.

Definition pr1_pfiber_loops_functor {A B} (f : A ->* B)
  : loops_functor (pfib f) o* pfiber_loops_functor f
    ==* pfib (loops_functor f).
Proof.
  serapply Build_pHomotopy.
  - intros [u v].
    refine (concat_1p _ @ concat_p1 _ @ _).
    exact (@ap_pr1_path_sigma _ _ (point A; point_eq f) (point A;point_eq f) _ _).
  - abstract (pointed_reduce; reflexivity).
Defined.

Definition pfiber_iterated_loops_functor {A B : pType} (n : nat) (f : A ->* B)
  : pfiber (iterated_loops_functor n f) <~>* iterated_loops n (pfiber f).
Proof.
  induction n.
  1: reflexivity.
  refine (_ o*E pfiber_loops_functor _ ).
  apply pequiv_loops_functor.
  apply IHn.
Defined.

(* a version of functor_hfiber which is functorial in both the function and the point *)
Definition functor_hfiber2 {A B C D}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : k o f == g o h) {b : B} {b' : D} (q : k b = b')
: hfiber f b -> hfiber g b'.
Proof.
  serapply functor_sigma.
  - exact h.
  - intros a e. exact ((p a)^ @ ap k e @ q).
Defined.

Definition functor_pfiber {A B C D}
           {f : A ->* B} {g : C ->* D} {h : A ->* C} {k : B ->* D}
           (p : k o* f ==* g o* h)
  : pfiber f ->* pfiber g.
Proof.
  serapply Build_pMap.
  + cbn. refine (functor_hfiber2 p (point_eq k)).
  + serapply path_hfiber. 
    - apply point_eq.
    - refine (concat_pp_p _ _ _ @ _). apply moveR_Vp. apply (point_htpy p)^.
Defined.

Definition pequiv_pfiber {A B C D}
           {f : A ->* B} {g : C ->* D} (h : A <~>* C) (k : B <~>* D)
           (p : k o* f ==* g o* h)
  : pfiber f <~>* pfiber g
  := Build_pEquiv _ _ (functor_pfiber p) _.

Definition square_functor_pfiber {A B C D}
           {f : A ->* B} {g : C ->* D} {h : A ->* C} {k : B ->* D}
           (p : k o* f ==* g o* h)
  : h o* pfib f ==* pfib g o* functor_pfiber p.
Proof.
  serapply Build_pHomotopy.
  - intros x; reflexivity.
  - apply moveL_pV. cbn; unfold functor_sigma; cbn.
    abstract (rewrite ap_pr1_path_sigma, concat_p1; reflexivity).
Defined.

Definition square_pequiv_pfiber {A B C D}
           {f : A ->* B} {g : C ->* D} (h : A <~>* C) (k : B <~>* D)
           (p : k o* f ==* g o* h)
  : h o* pfib f ==* pfib g o* pequiv_pfiber h k p
  := square_functor_pfiber p.

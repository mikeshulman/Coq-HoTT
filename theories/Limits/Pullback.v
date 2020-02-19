(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.
Require Import Fibrations EquivalenceVarieties Cubical.PathSquare.

Local Open Scope path_scope.

(** * Pullbacks *)

(** The pullback as an object *)
Definition Pullback {A B C} (f : B -> A) (g : C -> A)
  := { b : B & { c : C & f b = g c }}.

Global Arguments Pullback {A B C}%type_scope (f g)%function_scope.

(** The universal commutative square *)
Definition pullback_pr1 {A B C} {f : B -> A} {g : C -> A}
: Pullback f g -> B := (fun z => z.1).
Definition pullback_pr2 {A B C} {f : B -> A} {g : C -> A}
: Pullback f g -> C := (fun z => z.2.1).
Definition pullback_commsq {A B C} (f : B -> A) (g : C -> A)
: f o pullback_pr1 == g o pullback_pr2
:= (fun z => z.2.2).

(** The universally induced map into it by any commutative square *)
Definition pullback_corec {A B C D}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : k o f == g o h)
: A -> Pullback k g
:= fun a => (f a ; h a ; p a).

(** Symmetry of the pullback *)
Definition equiv_pullback_symm {A B C} (f : B -> A) (g : C -> A)
: Pullback f g <~> Pullback g f.
Proof.
  refine (_ oE equiv_sigma_symm (fun b c => f b = g c)).
  apply equiv_functor_sigma_id; intros c.
  apply equiv_functor_sigma_id; intros b.
  apply equiv_path_inverse.
Defined.

(** Pullback over [Unit] is equivalent to a product. *)
Definition equiv_pullback_unit_prod (A B : Type)
: Pullback (@const A Unit tt) (@const B Unit tt) <~> A * B.
Proof.
  simple refine (equiv_adjointify _ _ _ _).
  - intros [a [b _]]; exact (a , b).
  - intros [a b]; exact (a ; b ; 1).
  - intros [a b]; exact 1.
  - intros [a [b p]]; simpl.
    apply (path_sigma' _ 1); simpl.
    apply (path_sigma' _ 1); simpl.
    apply path_contr.
Defined.

(** The property of a given commutative square being a pullback *)
Definition IsPullback {A B C D}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : k o f == g o h)
  := IsEquiv (pullback_corec p).

Definition equiv_ispullback {A B C D}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : k o f == g o h) (ip : IsPullback p)
  : A <~> Pullback k g
  := Build_Equiv _ _ (pullback_corec p) ip.

(** This is equivalent to the transposed square being a pullback. *)
Definition ispullback_symm {A B C D}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : g o h == k o f) (pb : IsPullback (fun a => (p a)^))
  : IsPullback p.
Proof.
  rapply (cancelL_isequiv (equiv_pullback_symm g k)).
  apply pb.
Defined.

(** The pullback of the projections [{d:D & P d} -> D <- {d:D & Q d}] is equivalent to [{d:D & P d * Q d}]. *)
Definition ispullback_sigprod {D : Type} (P Q : D -> Type)
  : IsPullback (fun z:{d:D & P d * Q d} => 1%path : (z.1;fst z.2).1 = (z.1;snd z.2).1).
Proof.
  srapply isequiv_adjointify.
  - intros [[d1 p] [[d2 q] e]]; cbn in e.
    exists d1. exact (p, e^ # q).
  - intros [[d1 p] [[d2 q] e]]; unfold pullback_corec; cbn in *.
    destruct e; reflexivity.
  - intros [d [p q]]; reflexivity.
Defined.

Definition equiv_sigprod_pullback {D : Type} (P Q : D -> Type)
  : {d:D & P d * Q d} <~> Pullback (@pr1 D P) (@pr1 D Q)
  := Build_Equiv _ _ _ (ispullback_sigprod P Q).

(** For any commutative square, the fiber of the fibers is equivalent to the fiber of the "gap map" [pullback_corec]. *)
Definition hfiber_pullback_corec {A B C D}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : k o f == g o h) (b : B) (c : C) (q : k b = g c)
  : hfiber (pullback_corec p) (b; c; q) <~> hfiber (functor_hfiber p b) (c; q^).
Proof.
  unfold hfiber, functor_hfiber, functor_sigma.
  refine (equiv_sigma_assoc _ _ oE _).
  apply equiv_functor_sigma_id; intros a; cbn.
  refine (_ oE (equiv_path_sigma _ _ _)^-1); cbn.
  apply equiv_functor_sigma_id; intro p0; cbn.
  rewrite transport_sigma'; cbn.
  refine ((equiv_path_sigma _ _ _) oE _ oE (equiv_path_sigma _ _ _)^-1); cbn.
  apply equiv_functor_sigma_id; intro p1; cbn.
  rewrite !transport_paths_Fr, !transport_paths_Fl.
  refine (_ oE (equiv_ap (equiv_path_inverse _ _) _ _)); cbn.
  apply equiv_concat_l.
  refine (_ @ (inv_pp _ _)^).  apply whiskerL.
  refine (_ @ (inv_pp _ _)^).  apply whiskerL.
  symmetry; apply inv_V.
Defined.

(** If the induced map on fibers is an equivalence, then a square is a pullback. *)
Definition ispullback_isequiv_functor_hfiber {A B C D}
           {f : A -> B} {g : C -> D} {h : A -> C} {k : B -> D}
           (p : k o f == g o h)
           (e : forall b:B, IsEquiv (functor_hfiber p b))
  : IsPullback p.
Proof.
  unfold IsPullback.
  apply isequiv_fcontr; intro x.
  rapply contr_equiv'.
  - symmetry; apply hfiber_pullback_corec.
  - apply fcontr_isequiv, e.
Defined.

(** The pullback of a map along another one *)
Definition pullback_along {A B C} (f : B -> A) (g : C -> A)
: Pullback f g -> B
  := pr1.

Notation "f ^*" := (pullback_along f) : function_scope.

Definition hfiber_pullback_along {A B C} (f : B -> A) (g : C -> A) (b:B)
: hfiber (f ^* g) b <~> hfiber g (f b).
Proof.
  unfold hfiber, Pullback.
  refine (_ oE (equiv_sigma_assoc _ _)^-1).
  simpl.
  refine (_ oE equiv_functor_sigma_id _).
  2:intros; apply equiv_sigma_symm0.
  refine (_ oE equiv_sigma_assoc' _ _).
  refine (_ oE equiv_contr_sigma _).
  exact (equiv_functor_sigma_id (fun c => equiv_path_inverse _ _)).
Defined.

(** And the dual sort of pullback *)
Definition pullback_along' {A B C} (g : C -> A) (f : B -> A)
: Pullback f g -> C
  := fun z => z.2.1.

Arguments pullback_along' / .

Notation "g ^*'" := (pullback_along' g) : function_scope.

Definition hfiber_pullback_along' {A B C} (g : C -> A) (f : B -> A) (c:C)
: hfiber (g ^*' f) c <~> hfiber f (g c).
Proof.
  unfold hfiber, Pullback.
  refine (_ oE (equiv_sigma_assoc _ _)^-1).
  apply equiv_functor_sigma_id; intros b.
  refine (_ oE (equiv_sigma_assoc _ _)^-1).
  simpl.
  refine (_ oE equiv_functor_sigma_id _).
  2:intros; apply equiv_sigma_symm0.
  refine (_ oE equiv_sigma_assoc' _ _).
  refine (_ oE equiv_contr_sigma _).
  apply equiv_idmap.
Defined.

Section Functor_Pullback.

  Context {A1 B1 C1 A2 B2 C2}
          (f1 : B1 -> A1) (g1 : C1 -> A1)
          (f2 : B2 -> A2) (g2 : C2 -> A2)
          (h : A1 -> A2) (k : B1 -> B2) (l : C1 -> C2)
          (p : f2 o k == h o f1) (q : g2 o l == h o g1).

  Definition functor_pullback : Pullback f1 g1 -> Pullback f2 g2
    := functor_sigma k
        (fun b1 => (functor_sigma l
                     (fun c1 e1 => p b1 @ ap h e1 @ (q c1)^))).

  Definition hfiber_functor_pullback (z : Pullback f2 g2)
  : hfiber functor_pullback z
    <~> Pullback (transport (hfiber h) z.2.2 o functor_hfiber (k := f2) p z.1)
                 (functor_hfiber q z.2.1).
  Proof.
    destruct z as [b2 [c2 e2]].
    refine (_ oE hfiber_functor_sigma _ _ _ _ _ _).
    apply equiv_functor_sigma_id.
    intros [b1 e1]; simpl.
    refine (_ oE (equiv_transport _ _ _ (transport_sigma' e1^ (c2; e2)))).
    refine (_ oE hfiber_functor_sigma _ _ _ _ _ _); simpl.
    apply equiv_functor_sigma_id.
    intros [c1 e3]; simpl.
    refine (_ oE (equiv_transport _ _ _
                   (ap (fun e => e3^ # e) (transport_paths_Fl e1^ e2)))).
    refine (_ oE (equiv_transport _ _ _ (transport_paths_Fr e3^ _))).
    unfold functor_hfiber; simpl.
    refine (equiv_concat_l (transport_sigma' e2 _) _ oE _); simpl.
    refine (equiv_path_sigma _ _ _ oE _); simpl.
    apply equiv_functor_sigma_id; intros e0; simpl.
    refine (equiv_concat_l (transport_paths_Fl e0 _) _ oE _).
    refine (equiv_concat_l (whiskerL (ap h e0)^ (transport_paths_r e2 _)) _ oE _).
    refine (equiv_moveR_Vp _ _ _ oE _).
    refine (equiv_concat_l (concat_pp_p _ _ _) _ oE _).
    refine (equiv_moveR_Vp _ _ _ oE _).
    do 2 refine (equiv_concat_r (concat_pp_p _ _ _) _ oE _).
    refine (equiv_moveL_pM _ _ _ oE _).
    abstract (rewrite !ap_V, inv_V; refine (equiv_path_inverse _ _)).
  Defined.

End Functor_Pullback.

Section EquivPullback.
  Context {A B C f g A' B' C' f' g'}
          (eA : A <~> A') (eB : B <~> B') (eC : C <~> C')
          (p : f' o eB == eA o f) (q :  g' o eC == eA o g).

  Lemma equiv_pullback
    : Pullback f g <~> Pullback f' g'.
  Proof.
    unfold Pullback.
    apply (equiv_functor_sigma' eB); intro b.
    apply (equiv_functor_sigma' eC); intro c.
    refine (equiv_concat_l (p _) _ oE _).
    refine (equiv_concat_r (q _)^ _ oE _).
    refine (equiv_ap' eA _ _).
  Defined.

End EquivPullback.


(** Pullbacks commute with sigmas *)
Section PullbackSigma.

  Context
    {X Y Z : Type}
    {A : X -> Type} {B : Y -> Type} {C : Z -> Type}
    (f : Y -> X) (g : Z -> X)
    (r : forall x, B x -> A (f x))
    (s : forall x, C x -> A (g x)).

  Definition equiv_sigma_pullback
    : {p : Pullback f g & Pullback (transport A p.2.2 o r p.1) (s p.2.1)}
      <~> Pullback (functor_sigma f r) (functor_sigma g s).
  Proof.
    refine (_ oE (equiv_sigma_assoc _ _)^-1).
    refine (equiv_sigma_assoc _ _ oE _).
    apply equiv_functor_sigma_id; intro y.
    refine (_ oE (equiv_sigma_assoc _ _)^-1).
    refine (equiv_functor_sigma_id _ oE _).
    1: intro; apply equiv_sigma_assoc.
    refine (equiv_sigma_symm _ oE _).
    refine (equiv_functor_sigma_id _); intro z.
    refine (_ oE _).
    { refine (equiv_functor_sigma_id _); intro b.
      refine (equiv_functor_sigma_id _); intro c.
      apply equiv_path_sigma. }
    refine (equiv_functor_sigma_id _ oE _).
    1: intro b; cbn; apply equiv_sigma_symm.
    cbn; apply equiv_sigma_symm.
  Defined.

End PullbackSigma.

Definition issig_pullback {A B C : Type} (f : B -> A) (g : C -> A) :
  { b : B & { c : C & f b = g c }} <~> Pullback f g := reflexivity _.

Definition equiv_path_pullback {A B C : Type} {f : B -> A} {g : C -> A}
  (x y : Pullback f g) : 
  ({ p : x.1 = y.1 & { q : x.2.1 = y.2.1 & PathSquare x.2.2 y.2.2 (ap f p) (ap g q) }}) 
  <~> x = y.
Proof.
  destruct x as [b [c p]], y as [b' [c' p']]. simpl.
  refine (equiv_path_sigma _ _ _ oE _).
  apply equiv_functor_sigma_id. intros q. destruct q. simpl.
  refine (equiv_path_sigma _ _ _ oE _).
  apply equiv_functor_sigma_id. intros q. destruct q. simpl.
  symmetry. exact (Build_Equiv _ _ _ isequiv_sq_G1).
Defined.

Definition path_pullback_hset {A B C : Type} `{IsHSet A} (f : B -> A) (g : C -> A)
  {p q : Pullback f g} (s : p.1 = q.1) (t : p.2.1 = q.2.1) : p = q.
Proof.
  destruct p as [a [b p]], q as [c [d q]].
  apply (path_sigma _ _ _ s).
  cbn in *.
  destruct s.
  cbn.
  srapply path_sigma.
  1: apply t.
  srapply path_ishprop.
Defined.

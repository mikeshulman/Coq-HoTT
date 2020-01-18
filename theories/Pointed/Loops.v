Require Import HoTT.Basics HoTT.Types.
Require Import HSet Fibrations Factorization HoTT.Truncations HProp.
Require Import UnivalenceImpliesFunext.
Require Import Pointed.Core Pointed.pMap Pointed.pEquiv Pointed.pHomotopy.
Require Import WildCat Pointed.pType.

Import TrM.

Local Open Scope pointed_scope.
Local Open Scope path_scope.

(** ** Loop spaces *)

(** The type [x = x] is pointed. *)
Global Instance ispointed_loops A (a : A) : IsPointed (a = a) := 1.

Definition loops (A : pType) : pType
  := Build_pType (point A = point A) _.

Fixpoint iterated_loops (n : nat) (A : pType) : pType
  := match n with
       | O => A
       | S p => loops (iterated_loops p A)
     end.

(* Inner unfolding for iterated loops *)
Lemma unfold_iterated_loops (n : nat) (X : pType)
  : iterated_loops n.+1 X = iterated_loops n (loops X).
Proof.
  induction n.
  1: reflexivity.
  change (iterated_loops n.+2 X)
    with (loops (iterated_loops n.+1 X)).
  by refine (ap loops IHn @ _).
Defined.

(** The loop space decreases the truncation level by one.  We don't bother making this an instance because it is automatically found by typeclass search, but we record it here in case anyone is looking for it. *)
Definition istrunc_loops {n} (A : pType) `{IsTrunc n.+1 A}
  : IsTrunc n (loops A) := _.

(** Similarly for connectedness. *)
Definition isconnected_loops `{Univalence} {n} (A : pType)
  `{IsConnected n.+1 A} : IsConnected n (loops A) := _.

(** ** Functoriality of loop spaces *)

Definition loops_functor {A B : pType} (f : A ->* B)
  : (loops A) ->* (loops B).
Proof.
  refine (Build_pMap (loops A) (loops B)
            (fun p => (point_eq f)^ @ (ap f p @ point_eq f)) _).
  refine (_ @ concat_Vp (point_eq f)).
  apply whiskerL. apply concat_1p.
Defined.

Definition iterated_loops_functor {A B : pType} (n : nat)
  : (A ->* B) -> (iterated_loops n A) ->* (iterated_loops n B).
Proof.
  induction n as [|n IHn].
  1: exact idmap.
  refine (loops_functor o _).
  apply IHn.
Defined.

(* Loops functor respects composition *)
Definition loops_functor_compose {A B C : pType} (g : B ->* C) (f : A ->* B)
  : (loops_functor (pmap_compose g f))
  ==* (pmap_compose (loops_functor g) (loops_functor f)).
Proof.
  serapply Build_pHomotopy.
  { intros p. cbn.
    refine ((inv_pp _ _ @@ 1) @ concat_pp_p _ _ _ @ _).
    apply whiskerL.
    refine (((ap_V _ _)^ @@ 1) @ _ @ concat_p_pp _ _ _ @ ((ap_pp _ _ _)^ @@ 1)).
    apply whiskerL.
    refine (_ @ concat_p_pp _ _ _ @ ((ap_pp _ _ _)^ @@ 1)).
    apply whiskerR.
    apply ap_compose. }
  by pointed_reduce.
Defined.

(* Loops functor respects identity *)
Definition loops_functor_idmap (A : pType)
  : loops_functor (@pmap_idmap A) ==* pmap_idmap.
Proof.
  serapply Build_pHomotopy.
  { intro p.
    refine (concat_1p _ @ concat_p1 _ @ ap_idmap _). }
  reflexivity.
Defined.

(* Loops functor distributes over concatenation *)
Lemma loops_functor_pp {X Y : pType} (f : pMap X Y) (x y : loops X)
  : loops_functor f (x @ y) = loops_functor f x @ loops_functor f y.
Proof.
  pointed_reduce.
  apply ap_pp.
Defined.

Lemma loops_functor_pconst {A B : pType} : loops_functor (@pConst A B) ==* pConst.
Proof.
  serapply Build_pHomotopy.
  + intro p. refine (concat_1p _ @ concat_p1 _ @ ap_const _ _).
  + reflexivity.
Defined.

(* Loops functor preserves pointed homotopies *)
Definition loops_2functor {A B : pType} {f g : A ->* B} (p : f ==* g)
  : (loops_functor f) ==* (loops_functor g).
Proof.
  pointed_reduce.
  serapply Build_pHomotopy; cbn.
  { intro q.
    refine (_ @ (concat_p1 _)^ @ (concat_1p _)^).
    apply moveR_Vp, concat_Ap. }
  simpl. generalize (p ispointed_type0). generalize (g ispointed_type0).
  intros _ []. reflexivity.
Defined.

(* Iterated loops functor respects composition *)
Lemma iterated_loops_functor_compose n A B C (f : B ->* C)
  (g : A ->* B) : iterated_loops_functor n (f o* g)
  ==* (iterated_loops_functor n f) o* (iterated_loops_functor n g).
Proof.
  induction n as [|n IHn]; cbn.
  1: reflexivity.
  refine (_ @* (loops_functor_compose _ _)).
  apply loops_2functor, IHn.
Defined.

Lemma iterated_loops_functor_idmap (A : pType) n
  : iterated_loops_functor n (@pmap_idmap A) ==* pmap_idmap.
Proof.
  induction n; cbn.
  1: reflexivity.
  etransitivity.
  2: apply loops_functor_idmap.
  apply loops_2functor, IHn.
Defined.

Lemma iterated_loops_functor_pp {X Y : pType} (f : pMap X Y) n
  (x y : iterated_loops n.+1 X) : iterated_loops_functor n.+1 f (x @ y)
    = iterated_loops_functor n.+1 f x @ iterated_loops_functor n.+1 f y.
Proof.
  induction n.
  1: apply loops_functor_pp.
  change (iterated_loops_functor n.+2 f)
    with (loops_functor (iterated_loops_functor n.+1 f)).
  apply loops_functor_pp.
Defined.

(* Iterated loops functor respects homotopies *)
Definition iterated_loops_2functor n {A B : pType}
           {f g : A ->* B} (p : f ==* g)
  : (iterated_loops_functor n f) ==* (iterated_loops_functor n g).
Proof.
  induction n as [|n IHn]; [ assumption | apply loops_2functor, IHn ].
Defined.

(** The loop space functor decreases the truncation level by one.  *)
Global Instance istrunc_loops_functor {n} (A B : pType) (f : A ->* B)
  `{IsTruncMap n.+1 _ _ f} : IsTruncMap n (loops_functor f).
Proof.
  intro p.
  refine (trunc_equiv' _ (equiv_functor_sigma' 1
    (fun q => equiv_moveR_Vp _ _ _))).
  refine (trunc_equiv' _ (equiv_functor_sigma' 1
    (fun q => equiv_moveR_pM _ _ _))).
Defined.

(** And likewise the connectedness.  *)
(* Note: We give the definition explicitly since it was slow before. *)
Global Instance isconnected_loops_functor `{Univalence} {n : trunc_index}
  (A B : pType) (f : A ->* B) `{IsConnMap n.+1 _ _ f}
  : IsConnMap n (loops_functor f)
  := fun (p : loops B) =>
    isconnected_equiv' n _
      (equiv_functor_sigma' 1 (fun q => equiv_moveR_Vp _ p _))
      (isconnected_equiv' n _
        (equiv_functor_sigma' 1 (fun q => equiv_moveR_pM _ _ _))
        (isconnected_equiv' n _ (hfiber_ap _)^-1 (isconnected_paths _ _))).

(** It follows that loop spaces "commute with images". *)
Definition equiv_loops_image `{Univalence} n {A B : pType} (f : A ->* B)
  : loops (Build_pType (image n.+1 f) (factor1 (image n.+1 f) (point A)))
  <~> image n (loops_functor f).
Proof.
  set (C := (Build_pType (image n.+1 f) (factor1 (image n.+1 f) (point A)))).
  pose (g := Build_pMap A C (factor1 (image n.+1 f)) 1).
  pose (h := Build_pMap C B (factor2 (image n.+1 f)) (point_eq f)).
  transparent assert (I : (Factorization
    (@IsConnMap n) (@MapIn n) (loops_functor f))).
  { refine (@Build_Factorization (@IsConnMap n) (@MapIn n)
      (loops A) (loops B) (loops_functor f) (loops C)
      (loops_functor g) (loops_functor h) _ _ _).
    intros x; symmetry.
    refine (_ @ loops_functor_compose h g x).
    simpl.
    abstract (rewrite !concat_1p; reflexivity). }
  exact (path_intermediate (path_factor (O_factsys n) (loops_functor f) I
    (image n (loops_functor f)))).
Defined.

(** Loop inversion is a pointed equivalence *)
Definition loops_inv (A : pType) : loops A <~>* loops A.
Proof.
  serapply Build_pEquiv.
  1: exact (Build_pMap (loops A) (loops A) inverse 1).
  apply isequiv_path_inverse.
Defined.

(** Loops functor preserves equivalences *)
Definition pequiv_loops_functor {A B : pType}
  : A <~>* B -> loops A <~>* loops B.
Proof.
  intro f.
  serapply pequiv_adjointify.
  1: apply loops_functor, f.
  1: apply loops_functor, (pequiv_inverse f).
  1,2: refine ((loops_functor_compose _ _)^* @* _ @* loops_functor_idmap _).
  1,2: apply loops_2functor.
  1: apply peisretr.
  apply peissect.
Defined.

(** A version of [unfold_iterated_loops] that's an equivalence rather than an equality.  We could get this from the equality, but it's more useful to construct it explicitly since then we can reason about it.  *)
Definition unfold_iterated_loops' (n : nat) (X : pType)
  : iterated_loops n.+1 X <~>* iterated_loops n (loops X).
Proof.
  induction n.
  1: reflexivity.
  change (iterated_loops n.+2 X)
    with (loops (iterated_loops n.+1 X)).
  apply pequiv_loops_functor, IHn.
Defined.

(** For instance, we can prove that it's natural. *)
Definition unfold_iterated_loops_functor {A B : pType} (n : nat) (f : A ->* B)
  : (unfold_iterated_loops' n B) o* (iterated_loops_functor n.+1 f)
    ==* (iterated_loops_functor n (loops_functor f)) o* (unfold_iterated_loops' n A).
Proof.
  induction n.
  - srefine (Build_pHomotopy _ _).
    + reflexivity.
    + cbn. apply moveL_pV.
      refine (concat_1p _ @ _).
      refine (concat_1p _ @ _).
      refine (_ @ (concat_p1 _)^).
      exact ((ap_idmap _)^).
  - refine ((loops_functor_compose _ _)^* @* _).
    refine (_ @* (loops_functor_compose _ _)).
    apply loops_2functor.
    apply IHn.
Defined.

(** Iterated loops preserves equivalences *)
Lemma pequiv_iterated_loops_functor {A B} n : A <~>* B
  -> iterated_loops n A <~>* iterated_loops n B.
Proof.
  intros f.
  induction n.
  1: apply f.
  by apply pequiv_loops_functor.
Defined.

(** Since that was a separate induction, its underlying function is only homotopic to [iterated_loops_functor n], not definitionally equal. *)
Definition pequiv_iterated_loops_functor_is_iterated_loops_functor {A B} n (f : A <~>* B)
  : pequiv_iterated_loops_functor n f ==* iterated_loops_functor n f.
Proof.
  induction n as [|n IHn].
  - reflexivity.
  - apply loops_2functor, IHn.
Defined.

(* Loops preserves products *)
Lemma loops_prod (X Y : pType) : loops (X * Y) <~>* loops X * loops Y.
Proof.
  srefine (Build_pEquiv _ _ (Build_pMap _ _ (_ : Equiv _ _) _) _).
  1: symmetry; refine (equiv_path_prod (point _) (point (X * Y))).
  reflexivity.
Defined.

(* Iterated loops of products are products of iterated loops *)
Lemma iterated_loops_prod (X Y : pType) {n}
  : iterated_loops n (X * Y) <~>* (iterated_loops n X) * (iterated_loops n Y).
Proof.
  induction n.
  1: reflexivity.
  refine (pequiv_compose _ (loops_prod _ _)).
  by apply pequiv_loops_functor.
Defined.

(* A dependent form of loops *)
Definition loopsD {A} : pFam A -> pFam (loops A)
  := fun Pp => (fun q => transport Pp.1 q Pp.2 = Pp.2; 1).

Global Instance istrunc_pfam_loopsD {n} {A} (P : pFam A)
       {H :IsTrunc_pFam n.+1 P}
  : IsTrunc_pFam n (loopsD P).
Proof.
  intros a. pose (H (point A)). exact _.
Defined.

(* psigma and loops 'commute' *)
Lemma loops_psigma_commute (A : pType) (P : pFam A)
  : loops (psigma P) <~>* psigma (loopsD P).
Proof.
  srefine (Build_pEquiv _ _ (Build_pMap _ _ (_ : Equiv _ _) _) _).
  1: exact (equiv_path_sigma _ _ _)^-1%equiv.
  reflexivity.
Defined.

(* product and loops 'commute' *)
Lemma loops_pproduct_commute `{Funext} (A : Type) (F : A -> pType)
  : loops (pproduct F) <~>* pproduct (loops o F).
Proof.
  srefine (Build_pEquiv _ _ (Build_pMap _ _ (_ : Equiv _ _) _) _).
  1: apply equiv_apD10.
  reflexivity.
Defined.

(* product and iterated loops commute *)
Lemma iterated_loops_pproduct_commute `{Funext} (A : Type) (F : A -> pType) (n : nat)
  : iterated_loops n (pproduct F) <~>* pproduct (iterated_loops n o F).
Proof.
  induction n.
  1: reflexivity.
  refine (loops_pproduct_commute _ _ o*E _).
  apply pequiv_loops_functor, IHn.
Defined.

(* Loops neutralise sigmas when truncated *)
Lemma loops_psigma_trunc (n : nat) : forall (Aa : pType)
  (Pp : pFam Aa) (istrunc_Pp : IsTrunc_pFam (nat_to_trunc_index_2 n) Pp),
  iterated_loops n (psigma Pp)
  <~>* iterated_loops n Aa.
Proof.
  induction n.
  { intros A P p.
    srefine (Build_pEquiv _ _ (Build_pMap _ _ (_ : Equiv _ _) _) _).
    1: refine (@equiv_sigma_contr _ _ p).
    reflexivity. }
  intros A P p.
  refine (pequiv_inverse (unfold_iterated_loops' _ _) o*E _ o*E unfold_iterated_loops' _ _).
  refine (IHn _ _ _ o*E _).
  apply pequiv_iterated_loops_functor.
  apply loops_psigma_commute.
Defined.

(* We declare this local notation to make it easier to write pointed types *)
Local Notation "( X , x )" := (Build_pType X x).

(* We can convert between families of loops in a type and loops in Type at that type. *)
Definition loops_type `{Univalence} (A : Type)
  : loops (Type,A) <~>* (A <~> A, equiv_idmap).
Proof.
  apply issig_pequiv'.
  exists (equiv_equiv_path A A).
  reflexivity.
Defined.

Lemma local_global_looping `{Univalence} (A : Type) (n : nat)
  : iterated_loops n.+2 (Type, A)
  <~>* pproduct (fun a => iterated_loops n.+1 (A, a)).
Proof.
  induction n.
  { refine (_ o*E pequiv_loops_functor (loops_type A)).
    apply issig_pequiv'.
    exists (equiv_inverse (equiv_path_arrow 1%equiv 1%equiv)
            oE equiv_inverse (equiv_path_equiv 1%equiv 1%equiv)).
    reflexivity. }
  exact (loops_pproduct_commute _ _ o*E pequiv_loops_functor IHn).
Defined.

(* 7.2.7 *)
Theorem equiv_istrunc_istrunc_loops `{Univalence} n X
  : IsTrunc n.+2 X <~> forall x, IsTrunc n.+1 (loops (X, x)).
Proof.
  serapply equiv_iff_hprop.
  intro tr_loops.
  intros x y p.
  destruct p.
  apply tr_loops.
Defined.

(* This is slightly different to 7.2.9 in that we ommit n = -1, which is
   inhabited hsets are contractible. *)
Theorem equiv_istrunc_contr_iterated_loops `{Univalence} (n : nat)
  : forall A, IsTrunc n A <~> forall a : A,
    Contr (iterated_loops n.+1 (A, a)).
Proof.
  induction n.
  { intro A.
    refine (equiv_composeR' equiv_hset_axiomK _).
    refine (equiv_iff_hprop (fun K a => Build_Contr _ 1 (fun x => (K a x)^)) _).
    intros ? ? ?; apply path_contr. }
  intro A.
  transitivity (forall x, IsTrunc n (loops (A, x))).
  1: destruct n; apply equiv_istrunc_istrunc_loops.
  serapply equiv_functor_forall_id.
  intro a.
  apply (equiv_composeR' (IHn (loops (A, a)))).
  cbn; refine (equiv_iff_hprop _ _).
  1: change ((forall p : a = a, Contr ((iterated_loops n.+1 (loops (A, a), p))))
      -> Contr (iterated_loops n.+2 (A, a))).
  1: refine (fun X => (ap _ (unfold_iterated_loops n.+1 _))^ # X 1).
  change (Contr (iterated_loops n.+2 (A, a))
    -> (forall p : a = a, Contr ((iterated_loops n.+1 (loops (A, a), p))))).
  intros X p.
  refine (@contr_equiv' _ _ _ X).
  rewrite !unfold_iterated_loops.
  apply pointed_equiv_equiv.
  apply pequiv_iterated_loops_functor.
  symmetry.
  transitivity (p @ p^ = p @ p^, 1).
  { srefine (Build_pEquiv' _ _).
    1: exact (equiv_ap (equiv_concat_r _ _) _ _).
    reflexivity. }
  serapply Build_pEquiv'.
  { apply equiv_concat_lr.
    1: symmetry; apply concat_pV.
    apply concat_pV. }
  cbn; by rewrite concat_p1, concat_Vp.
Qed.

(** [loops] and [iterated_loops] are 1-functors *)
Global Instance is0functor_loops
  : Is0Functor loops.
Proof.
  apply Build_Is0Functor. intros. exact (loops_functor f).
Defined.

Global Instance is1functor_loops : Is1Functor loops.
Proof.
  apply Build_Is1Functor.
  + intros ? ? ? ? h. exact (loops_2functor h).
  + intros. apply loops_functor_idmap.
  + intros. apply loops_functor_compose.
Defined.

Global Instance is0functor_iterated_loops (n : nat)
  : Is0Functor (iterated_loops n).
Proof.
  apply Build_Is0Functor. intros. exact (iterated_loops_functor n f).
Defined.

Global Instance is1functor_iterated_loops (n : nat)
  : Is1Functor (iterated_loops n).
Proof.
  apply Build_Is1Functor.
  + intros ? ? ? ? h. exact (iterated_loops_2functor n h).
  + intros. apply iterated_loops_functor_idmap.
  + intros. apply iterated_loops_functor_compose.
Defined.

(** [loops_inv] is a natural transformation. *)
Global Instance is1natural_loops_inv : Is1Natural loops loops loops_inv.
Proof.
  apply Build_Is1Natural. intros A B f.
  serapply Build_pHomotopy.
  + intros p. refine (inv_Vp _ _ @ whiskerR _ (point_eq f) @ concat_pp_p _ _ _).
    refine (inv_pp _ _ @ whiskerL (point_eq f)^ (ap_V f p)^).
  + pointed_reduce. pointed_reduce. reflexivity.
Defined.

(** Loops on the pointed type of dependent pointed maps correspond to
  pointed dependent maps into a family of loops. *)
(* We define this in this direction, because the forward map is pointed by
  reflexivity. *)
Definition equiv_loops_ppforall `{Funext} {A : pType} (B : A -> pType)
  : loops (ppforall x : A, B x) <~>* (ppforall x : A, loops (B x)).
Proof.
  serapply Build_pEquiv'.
  1: symmetry; exact (equiv_path_pforall (point_pforall B) (point_pforall B)).
  reflexivity.
Defined.

(** We need a bunch of lemmas to prove that [equiv_loops_ppforall] is natural. *)

(** First we are going to generalize the underlying map of [loops_functor].
  The reason of this generalization is that the generalization takes a path
  instead of a loop, and therefore we can apply path induction.
  This is ported from Lean.*)

Definition ap_gen {A B : Type} (f : A -> B) {a a' : A}
  {b b' : B} (q : f a = b) (q' : f a' = b') (p : a = a')
  : b = b'
  := q^ @ (ap f p @ q').

Definition ap_gen_1 {A B : Type} (f : A -> B) {a : A} {b : B} (q : f a = b)
  : ap_gen f q q 1 = 1
  := whiskerL q^ (concat_1p q) @ concat_Vp q.

Definition ap_gen_con {A B : Type} (f : A -> B) {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
  (q₁ : f a₁ = b₁) (q₂ : f a₂ = b₂) (q₃ : f a₃ = b₃) (p₁ : a₁ = a₂) (p₂ : a₂ = a₃)
  : ap_gen f q₁ q₃ (p₁ @ p₂) = ap_gen f q₁ q₂ p₁ @ ap_gen f q₂ q₃ p₂.
Proof.
  induction p₂, q₃, q₂, q₁, p₁. reflexivity.
Defined.

Definition ap_gen_inv {A B : Type} (f : A -> B) {a₁ a₂ : A}
  {b₁ b₂ : B} (q₁ : f a₁ = b₁) (q₂ : f a₂ = b₂) (p₁ : a₁ = a₂)
  : ap_gen f q₂ q₁ p₁^ = (ap_gen f q₁ q₂ p₁)^.
Proof.
  induction p₁, q₁, q₂. reflexivity.
Defined.

Definition ap_gen_1_eq {A B : Type} (f : A -> B) {a : A} (q : f a = f a) (r : q = 1)
  : ap_gen_1 f q = ap (fun x => ap_gen f x x 1) r.
Proof.
  rewrite <- (inv_V r). induction r^. reflexivity.
Defined.

Definition natural_loops_ppforall_lem {A} {B C : pFam A}
  {f : forall (a : A), B a -> C a} {f₀ : f (point A) (dpoint B) = dpoint C}
  {k : pForall A B} {k' : pForall A C} (p : functor_pforall_right f f₀ k ==* k')
  : ap_gen (f (point _)) (p (point _)) f₀ (dpoint_eq k) = dpoint_eq k'.
Proof.
  symmetry.
  apply moveL_Vp.
  exact (point_htpy p).
Defined.

Definition natural_loops_ppforall_lem2 {A} {B C : pFam A}
  {f : forall (a : A), B a -> C a} {f₀ : f (point A) (dpoint B) = dpoint C} {k l : pForall A B}
  {k' l' : pForall A C} (p : functor_pforall_right f f₀ k ==* k')
  (q : functor_pforall_right f f₀ l ==* l')
  : ap_gen (f (point _)) (p (point _)) (q (point _)) (dpoint_eq k @ (dpoint_eq l)^) =
    dpoint_eq k' @ (dpoint_eq l')^.
Proof.
  refine (ap_gen_con (f (point _)) _ f₀ _ _ _ @ _).
  refine (natural_loops_ppforall_lem p @@ (ap_gen_inv _ _ _ _ @ inverse2 (natural_loops_ppforall_lem q))).
Defined.

(* This proof is very slow, and needs to be sped up *)
Definition natural_loops_ppforall_lem3 `{Funext} {A} {B C : pFam A}
  {f : forall (a : A), B a -> C a} {f₀ : f (point A) (dpoint B) = dpoint C} {k l : pForall A B}
  {k' l' : pForall A C} (p : functor_pforall_right f f₀ k ==* k')
  (q : functor_pforall_right f f₀ l ==* l')
  : Square (A := Type)
         (ap_gen (functor_pforall_right f f₀) (path_pforall p) (path_pforall q))
         (functor_pforall_right (B := (fun a => k a = l a; _))
                                (B' := (fun a => k' a = l' a; _))
            (fun a => ap_gen (f a) (p a) (q a))
            (natural_loops_ppforall_lem2 p q))
         phomotopy_path
         phomotopy_path.
Proof.
  intro r.
  induction r, C as [C c0], B as [B b0], k as [k k₀].
  simpl in f₀, f, k₀, k.
  induction f₀, k₀.
  revert l' q.
  (* I want to apply phomotopy_ind', but Coq cannot unify this with the goal
  when using [refine]. This is a workaround, which works in this case. *)
  serapply (phomotopy_ind _). cbn beta. rewrite path_pforall_1.
  revert k' p.
  serapply (phomotopy_ind _). cbn beta. rewrite path_pforall_1.
  reflexivity.
Defined.

(** Reducing the term obtained by rewrite. *)
Definition internal_paths_rew_r_unfold {A : Type} (P : A -> Type) {x y : A} (p : x = y) (u : P y)
  : internal_paths_rew_r A x y P u p = transport P p^ u.
Proof.
  induction p. reflexivity.
Defined.

(** Definitionally equal to f, but useful to state the next lemma. *)
Definition fiberwise_pmap_from_point {A : pType} {B : A -> Type} {C : A -> Type}
  (f : forall x, B x -> C x) (b0 : B (point A))
  : forall x, pfam_pr1 (B; b0) x -> pfam_pr1 (C; f _ b0) x
  := f.

(* Unfortunately, this lemma is very slow. The bottleneck is likely a bunch
  of definitional reduction. *)
Definition natural_loops_ppforall_lem3_refl `{Funext} {A : pType} {B C : A -> Type}
  (f : forall (a : A), B a -> C a) (k : forall a, B a)
  : natural_loops_ppforall_lem3
      (reflexivity (functor_pforall_right (fiberwise_pmap_from_point f (k _))
                                          1 (pforall_from_pointed k)))
      (reflexivity (functor_pforall_right (fiberwise_pmap_from_point f (k _))
                                          1 (pforall_from_pointed k)))
      1 = ap phomotopy_path (ap_gen_1 _ _).
Proof.
  refine (phomotopy_ind_1 _ _ @ _).
  refine (internal_paths_rew_r_unfold _ _ _ @ _).
  refine (ap (transport _ _) _ @ _).
  1: refine (phomotopy_ind_1 _ _ @ _).
  1: exact (internal_paths_rew_r_unfold _ _ _).
  refine ((transport_diagonal
    (fun p1 p2 => (phomotopy_path o ap_gen _ p1 p2) 1 = _) _ _)^ @ _).
  refine (transport_paths_Fl (f := fun p =>
    (phomotopy_path o ap_gen _ p p)  1) _ _ @ _).
  refine (concat_p1 _ @ _).
  (* refine (inverse2 (ap_V _ _) @ _). (*curiously this fails.*) *)
  rewrite ap_V, inv_V.
  refine (ap_compose (fun p => ap_gen _ p p 1) phomotopy_path path_pforall_1 @ _).
  refine ((ap _ (ap_gen_1_eq _ _ _))^).
Defined.

(** [equiv_loops_ppforall] is natural. *)
(* Unfortunately, this lemma is very slow. The bottleneck is likely a bunch
  of definitional reduction. *)
Definition natural_loops_ppforall_right `{Funext} {A : pType} {B B' : A -> pType}
  (f : forall a, B a ->* B' a)
  : Square (equiv_loops_ppforall B)
         (equiv_loops_ppforall B')
         (loops_functor (functor_ppforall_right f))
         (functor_ppforall_right (fun a => loops_functor (f a))).
Proof.
  apply transpose.
  revert B' f. refine (fiberwise_pointed_map_rec _ _). intros B' f.
  serapply Build_pHomotopy.
  + exact (natural_loops_ppforall_lem3
      (pmap_compose_ppforall_point (fun a => pmap_from_point (f a) (point _)))
      (pmap_compose_ppforall_point (fun a => pmap_from_point (f a) (point _)))).
  + refine ((concat_p1 _)^ @ (_ @@ _)).
    2: { refine ((inverse2 (concat_1p _ @ path_pforall_1))^). }
    unfold pmap_compose_ppforall_point.
    refine (natural_loops_ppforall_lem3_refl f (fun x => point (B x)) @ _).
    exact (concat_p1 _)^.
Defined.

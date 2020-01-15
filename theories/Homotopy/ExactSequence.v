(* -*- mode: coq; mode: visual-line -*-  *)
Require Import Basics.
Require Import Types.
Require Import SuccessorStructure.
Require Import Pointed.
Require Import ReflectiveSubuniverse Modality Modalities.Identity.
Require Import Truncations.
Require Import Fibrations EquivalenceVarieties.

Local Open Scope succ_scope.
Open Scope pointed_scope.

(** * Exact sequences *)

(** ** Modalities *)

(** The notion of exactness makes sense relative to any modality.  To state it in that level of generality would require module-type hackery.  But in practice we only want to apply it to the (-1)-truncation and to the identity modality.  Unfortunately none of the standard families of modalities includes both of those, but we can take a union of the truncation modalities with the identity modality. *)
Module TrId_Modalities :=  Modalities_FamUnion Truncation_Modalities Identity_Modalities.
Module Import TrIdM := Modalities_Theory TrId_Modalities.

(** Unfortunately this way we don't automatically inherit the useful shortcuts about truncation modalities, so we have to redefine some of them. *)
Global Instance issepfor_TrId (n : trunc_index) : IsSepFor (Tr n.+1) (Tr n).
Proof.
  intros A; split; intros; apply inO_tr_istrunc; exact _.
Defined.


(** ** Very short complexes *)

(** A (very short) complex is a pair of pointed maps whose composite is the zero map. *)
Notation IsComplex i f := (f o* i ==* pConst).

(** This induces a map from the domain of [i] to the fiber of [f]. *)
Definition cx_to_fiber {F X Y : pType} (i : F ->* X) (f : X ->* Y)
           (cx : IsComplex i f)
  : F ->* pfiber f.
Proof.
  srapply Build_pMap.
  - intros x; exact (i x ; cx x).
  - cbn. refine (path_sigma' _ (point_eq i) _); cbn.
    refine (transport_paths_Fl _ _ @ _).
    apply moveR_Vp.
    exact ((concat_p1 _)^ @ point_htpy cx).
Defined.

(** ...whose composite with the projection [pfib : pfiber i -> X] is [i].  *)
Definition pfib_cx_to_fiber {F X Y : pType} (i : F ->* X) (f : X ->* Y)
           (cx : IsComplex i f)
  : pfib f o* cx_to_fiber i f cx ==* i.
Proof.
  serapply Build_pHomotopy.
  - intros u; reflexivity.
  - cbn.
    rewrite ap_pr1_path_sigma; hott_simpl.
Defined.

(** Truncation preserves complexes. *)
Definition iscomplex_ptr (n : trunc_index)
       {F X Y : pType} (i : F ->* X) (f : X ->* Y) (cx : IsComplex i f)
  : IsComplex (ptr_functor n i) (ptr_functor n f).
Proof.
  refine ((ptr_functor_pmap_compose n i f)^* @* _).
  refine (_ @* ptr_functor_pconst n).
  apply ptr_functor_homotopy; assumption.
Defined.

(** Loopspaces preserve complexes. *)
Definition iscomplex_loops
       {F X Y : pType} (i : F ->* X) (f : X ->* Y) (cx : IsComplex i f)
  : IsComplex (loops_functor i) (loops_functor f).
Proof.
  refine ((loops_functor_compose f i)^* @* _ @* loops_functor_pconst).
  apply loops_2functor; assumption.
Defined.

Definition iscomplex_iterated_loops
           {F X Y : pType} (i : F ->* X) (f : X ->* Y)
           (cx : IsComplex i f) (n : nat)
  : IsComplex (iterated_loops_functor n i) (iterated_loops_functor n f).
Proof.
  induction n as [|n IHn]; [ exact cx | ].
  apply iscomplex_loops; assumption.
Defined.  

(** Passage across homotopies preserves complexes. *)
Definition iscomplex_homotopic_i {F X Y : pType}
           {i i' : F ->* X} (ii : i' ==* i) (f : X ->* Y) (cx : IsComplex i f)
  : IsComplex i' f.
Proof.
  exact (pmap_postwhisker f ii @* cx).
Defined.

Definition iscomplex_homotopic_f {F X Y : pType}
           (i : F ->* X) {f f' : X ->* Y} (ff : f' ==* f) (cx : IsComplex i f)
  : IsComplex i f'.
Proof.
  exact (pmap_prewhisker i ff @* cx).
Defined.


(** ** Very short exact sequences and fiber sequences *)

(** A complex is n-exact if the induced map [cx_to_fiber] is n-connected.  *)
Class IsExact (n : Modality) {F X Y : pType} (i : F ->* X) (f : X ->* Y) :=
{
  cx_isexact : IsComplex i f ;
  conn_map_isexact : IsConnMap n (cx_to_fiber i f cx_isexact)
}.

Global Existing Instance conn_map_isexact.

(** Passage across homotopies preserves exactness. *)
Definition isexact_homotopic_i n  {F X Y : pType}
           {i i' : F ->* X} (ii : i' ==* i) (f : X ->* Y)
           `{IsExact n F X Y i f}
  : IsExact n i' f.
Proof.
  exists (iscomplex_homotopic_i ii f cx_isexact).
  refine (conn_map_homotopic n (cx_to_fiber i f cx_isexact) _ _ _).
  intros u; cbn.
  refine (path_sigma' _ (ii u)^ _).
  exact (transport_paths_Fl _ _ @ ((inverse2 (ap_V _ _) @ inv_V _) @@ 1)).
Defined.  

(** When [n] is the identity modality, so that [cx_to_fiber] is an equivalence, we get simply a fiber sequence.  Fiber sequences can alternatively be defined as an equivalence to the fiber of some map. *)
Definition FiberSeq (F X Y : pType) := { f : X ->* Y & F <~>* pfiber f }.

Definition i_fiberseq {F X Y} (fs : FiberSeq F X Y)
  : F ->* X
  := pfib fs.1 o* fs.2.

Global Instance isexact_oo_fiberseq {F X Y : pType} (fs : FiberSeq F X Y)
  : IsExact oo (i_fiberseq fs) fs.1.
Proof.
  srapply Build_IsExact; [ serapply Build_pHomotopy | ].
  - intros u; cbn. 
    exact ((fs.2 u).2).
  - cbn.
    refine (concat_p1 _ @ _).
    apply moveL_Mp.
    refine (_ @ (point_eq fs.2)..2).
    refine (_ @ (transport_paths_Fl _ _)^).
    apply whiskerR, inverse2, ap, concat_p1.
  - intros [x p].
    apply fcontr_isequiv.
    change (IsEquiv fs.2); exact _.
Defined.

Definition fiberseq_isexact_oo {F X Y : pType} (i : F ->* X) (f : X ->* Y)
           `{IsExact oo F X Y i f}
  : FiberSeq F X Y.
Proof.
  exists f.
  refine (Build_pEquiv _ _ (cx_to_fiber i f cx_isexact) _).
  apply isequiv_fcontr; intros u. 
  rapply conn_map_isexact.
Defined.

(** It's easier to show that loops preserve fiber sequences than that they preserve oo-exact sequences. *)
Definition fiberseq_loops {F X Y} (fs : FiberSeq F X Y)
  : FiberSeq (loops F) (loops X) (loops Y).
Proof.
  exists (loops_functor fs.1).
  refine (_ o*E pequiv_loops_functor fs.2).
  exact ((pfiber_loops_functor fs.1)^-1* ).
Defined.

(** Now we can deduce that they preserve oo-exact sequences.  The hardest part is modifying the first map back to [loops_functor i]. *)
Global Instance isexact_loops {F X Y} (i : F ->* X) (f : X ->* Y)
           `{IsExact oo F X Y i f}
  : IsExact oo (loops_functor i) (loops_functor f).
Proof.
  refine (@isexact_homotopic_i
            oo _ _ _ _ (loops_functor i) _ (loops_functor f)
            (isexact_oo_fiberseq (fiberseq_loops (fiberseq_isexact_oo i f)))).
  transitivity (loops_functor (pfib f) o* loops_functor (cx_to_fiber i f cx_isexact)).
  - refine (_ @* loops_functor_compose _ _).
    apply loops_2functor.
    symmetry; apply pfib_cx_to_fiber.
  - refine (_ @* pmap_compose_assoc _ _ _).
    refine (pmap_prewhisker (loops_functor (cx_to_fiber i f cx_isexact)) _).
    apply moveR_pequiv_fV.
    apply pr1_pfiber_loops_functor.
Defined.

Global Instance isexact_iterated_loops {F X Y} (i : F ->* X) (f : X ->* Y)
           `{IsExact oo F X Y i f} (n : nat)
  : IsExact oo (iterated_loops_functor n i) (iterated_loops_functor n f).
Proof.
  induction n as [|n IHn]; [ assumption | apply isexact_loops; assumption ].
Defined.

(** (n.+1)-truncation preserves n-exactness. *)
Definition isexact_ptr (n : trunc_index)
           {F X Y : pType} (i : F ->* X) (f : X ->* Y)
           `{IsExact (Tr n) F X Y i f}
  : IsExact (Tr n) (ptr_functor n.+1 i) (ptr_functor n.+1 f).
Proof.
  exists (iscomplex_ptr n.+1 i f cx_isexact).
  simple notypeclasses refine
    (cancelR_conn_map (Tr n) (@tr n.+1 F) 
      (cx_to_fiber (ptr_functor n.+1 i) (ptr_functor n.+1 f) _)).
  { intros x; rapply isconnected_pred. }
  refine (conn_map_homotopic (Tr n) _ _ _
           (conn_map_compose (Tr n) (cx_to_fiber i f _)
             (functor_hfiber (fun y => (to_O_natural (Tr n.+1) f y)^) (point Y)))).
  intros x; refine (path_sigma' _ 1 _); cbn.
  (* This is even simpler than it looks, because for truncations [to_O_natural n.+1 := 1], [to n.+1 := tr], and [cx_const := H]. *)
  exact (1 @@ (concat_p1 _)^).
Defined.

(** In particular, (n.+1)-truncation takes fiber sequences to n-exact ones. *)
Definition isexact_ptr_oo (n : trunc_index)
           {F X Y : pType} (i : F ->* X) (f : X ->* Y) `{IsExact oo F X Y i f}
  : IsExact (Tr n) (ptr_functor n.+1 i) (ptr_functor n.+1 f).
Proof.
  rapply isexact_ptr.
  exists cx_isexact.
  intros z; apply isconnected_contr.
  exact (conn_map_isexact (f := f) (i := i) z).
Defined.


(** ** Connecting maps *)

(** The connecting maps for the long exact sequence of loop spaces. *)
Definition connect {F X Y} (fs : FiberSeq F X Y)
  : loops Y ->* F.
Proof.
  srapply Build_pMap.
  - intros p. apply (fs.2)^-1.
    exists (point X).
    exact (point_eq fs.1 @ p).
  - cbn.
    apply moveR_equiv_V.
    refine (_ @ (point_eq fs.2)^).
    exact (path_sigma' _ 1 (concat_p1 _)).
Defined.

Global Instance isexact_connect_L {F X Y} (i : F ->* X) (f : X ->* Y)
       `{IsExact oo F X Y i f}
  : IsExact oo (connect (fiberseq_isexact_oo i f)) i.
Admitted.

Global Instance isexact_connect_R {F X Y} (i : F ->* X) (f : X ->* Y)
       `{IsExact oo F X Y i f}
  : IsExact oo (loops_functor f) (connect (fiberseq_isexact_oo i f)).
Admitted.

(** ** Long exact sequences *)

Record LongExactSequence (k : Modality) (N : SuccStr) : Type :=
{
  les_carrier : N -> pType;
  les_fn : forall n, les_carrier n.+1 ->* les_carrier n;
  les_isexact : forall n, IsExact k (les_fn n.+1) (les_fn n)
}.

Coercion les_carrier : LongExactSequence >-> Funclass.
Global Existing Instance les_isexact.

Local Notation "'0'" := (inl (inl (inr tt))).
Local Notation "'1'" := (inl (inr tt)).
Local Notation "'2'" := (inr tt).

Definition loops_carrier (F X Y : pType) (n : N3) : pType :=
  match n with
  | (n, inl (inl (inl x))) => Empty_ind _ x
  | (n, 0) => iterated_loops n Y
  | (n, 1) => iterated_loops n X
  | (n, 2) => iterated_loops n F
  end.

(** Starting from a fiber sequence, we can obtain a long oo-exact sequence of loop spaces. *)
Definition loops_les {F X Y : pType} (i : F ->* X) (f : X ->* Y)
           `{IsExact oo F X Y i f}
  : LongExactSequence oo (N3).
Proof.
  srefine (Build_LongExactSequence oo (N3) (loops_carrier F X Y) _ _).
  all:intros [n [[[[]|[]]|[]]|[]]]; cbn.
  { exact (iterated_loops_functor n f). }
  { exact (iterated_loops_functor n i). }
  { exact (connect (fiberseq_isexact_oo (iterated_loops_functor n i)
                                        (iterated_loops_functor n f))). }
  all:exact _.
Defined.

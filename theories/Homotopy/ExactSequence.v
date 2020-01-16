(* -*- mode: coq; mode: visual-line -*-  *)
Require Import Basics.
Require Import Types.
Require Import SuccessorStructure.
Require Import WildCat.
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
Definition IsComplex {F X Y} (i : F ->* X) (f : X ->* Y)
  := (f o* i ==* pConst).

(** This induces a map from the domain of [i] to the fiber of [f]. *)
Definition cxfib {F X Y : pType} {i : F ->* X} {f : X ->* Y}
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
Definition pfib_cxfib {F X Y : pType} {i : F ->* X} {f : X ->* Y}
           (cx : IsComplex i f)
  : pfib f o* cxfib cx ==* i.
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

(** And likewise passage across squares with equivalences *)
Definition iscomplex_squaric_i {F F' X X' Y : pType}
           (i : F ->* X) (i' : F' ->* X')
           (g : F' <~>* F) (h : X' <~>* X) (p : Square i' i g h)
           (f : X ->* Y)
           (cx: IsComplex i f)
  : IsComplex i' (f o* h).
Proof.
  refine (pmap_compose_assoc _ _ _ @* _).
  refine (pmap_postwhisker f p @* _).
  refine ((pmap_compose_assoc _ _ _)^* @* _).
  refine (pmap_prewhisker g cx @* _).
  apply postcompose_pconst.
Defined.


(** ** Very short exact sequences and fiber sequences *)

(** A complex is n-exact if the induced map [cxfib] is n-connected.  *)
Class IsExact (n : Modality) {F X Y : pType} (i : F ->* X) (f : X ->* Y) :=
{
  cx_isexact : IsComplex i f ;
  conn_map_isexact : IsConnMap n (cxfib cx_isexact)
}.

Global Existing Instance conn_map_isexact.

(** Passage across homotopies preserves exactness. *)
Definition isexact_homotopic_i n  {F X Y : pType}
           {i i' : F ->* X} (ii : i' ==* i) (f : X ->* Y)
           `{IsExact n F X Y i f}
  : IsExact n i' f.
Proof.
  exists (iscomplex_homotopic_i ii f cx_isexact).
  refine (conn_map_homotopic n (cxfib cx_isexact) _ _ _).
  intros u; cbn.
  refine (path_sigma' _ (ii u)^ _).
  exact (transport_paths_Fl _ _ @ ((inverse2 (ap_V _ _) @ inv_V _) @@ 1)).
Defined.  

(** And also passage across squares with equivalences. *)
Definition isexact_squaric_i n  {F F' X X' Y : pType}
           (i : F ->* X) (i' : F' ->* X')
           (g : F' <~>* F) (h : X' <~>* X) (p : Square i' i g h)
           (f : X ->* Y)
           `{IsExact n F X Y i f}
  : IsExact n i' (f o* h).
Proof.
  exists (iscomplex_squaric_i i i' g h p f cx_isexact); cbn.
  simple notypeclasses refine (cancelR_equiv_conn_map n (C := pfiber f) _ _).
  - exact (@equiv_functor_hfiber _ _ _ _ (f o h) f h equiv_idmap
             (fun x => 1%path) (point Y)).
  - cbn; unfold functor_hfiber, functor_sigma; cbn.
    refine (conn_map_homotopic n (@cxfib _ _ _ i f cx_isexact o g) _ _ _).
    intros u; cbn.
    refine (path_sigma' _ (p u)^ _).
    abstract (
        rewrite transport_paths_Fl, ap_V, inv_V,
        !concat_1p, concat_p1, ap_idmap;
        reflexivity
      ).
Defined.


(** When [n] is the identity modality [oo], so that [cxfib] is an equivalence, we get simply a fiber sequence.  In particular, the fiber of a given map yields an oo-exact sequence. *)

Definition iscomplex_pfib {X Y} (f : X ->* Y)
  : IsComplex (pfib f) f.
Proof.
  serapply Build_pHomotopy.
  - intros [x p]; exact p.
  - cbn. exact (concat_p1 _ @ (concat_1p _)^).
Defined.

Global Instance isexact_pfib {X Y} (f : X ->* Y)
  : IsExact oo (pfib f) f.
Proof.
  exists (iscomplex_pfib f).
  exact _.
Defined.    

(** Fiber sequences can alternatively be defined as an equivalence to the fiber of some map. *)
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

Definition pequiv_cxfib {F X Y : pType} {i : F ->* X} {f : X ->* Y}
           `{IsExact oo F X Y i f}
  : F <~>* pfiber f.
Proof.
  refine (Build_pEquiv _ _ (cxfib cx_isexact) _).
  apply isequiv_fcontr; intros u. 
  rapply conn_map_isexact.
Defined.

Definition fiberseq_isexact_oo {F X Y : pType} (i : F ->* X) (f : X ->* Y)
           `{IsExact oo F X Y i f}
  : FiberSeq F X Y
  := (f ; pequiv_cxfib).

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
  transitivity (loops_functor (pfib f) o* loops_functor (cxfib cx_isexact)).
  - refine (_ @* loops_functor_compose _ _).
    apply loops_2functor.
    symmetry; apply pfib_cxfib.
  - refine (_ @* pmap_compose_assoc _ _ _).
    refine (pmap_prewhisker (loops_functor (cxfib cx_isexact)) _).
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
Global Instance isexact_ptr (n : trunc_index)
           {F X Y : pType} (i : F ->* X) (f : X ->* Y)
           `{IsExact (Tr n) F X Y i f}
  : IsExact (Tr n) (ptr_functor n.+1 i) (ptr_functor n.+1 f).
Proof.
  exists (iscomplex_ptr n.+1 i f cx_isexact).
  simple notypeclasses refine
    (cancelR_conn_map (Tr n) (@tr n.+1 F) 
      (@cxfib _ _ _ (ptr_functor n.+1 i) (ptr_functor n.+1 f) _)).
  { intros x; rapply isconnected_pred. }
  refine (conn_map_homotopic (Tr n) _ _ _
           (conn_map_compose (Tr n) (cxfib _)
             (functor_hfiber (fun y => (to_O_natural (Tr n.+1) f y)^) (point Y)))).
  intros x; refine (path_sigma' _ 1 _); cbn.
  (* This is even simpler than it looks, because for truncations [to_O_natural n.+1 := 1], [to n.+1 := tr], and [cx_const := H]. *)
  exact (1 @@ (concat_p1 _)^).
Defined.

(** In particular, (n.+1)-truncation takes fiber sequences to n-exact ones. *)
Global Instance isexact_ptr_oo (n : trunc_index)
           {F X Y : pType} (i : F ->* X) (f : X ->* Y) `{IsExact oo F X Y i f}
  : IsExact (Tr n) (ptr_functor n.+1 i) (ptr_functor n.+1 f).
Proof.
  rapply isexact_ptr.
  exists cx_isexact.
  intros z; apply isconnected_contr.
  exact (conn_map_isexact (f := f) (i := i) z).
Defined.


(** ** Connecting maps *)

Definition pequiv_pfiber' {A B C D}
           {f : A ->* B} {g : C ->* D} {h : A <~>* C} {k : B <~>* D}
           (p : Square f g h k)
  : pfiber f <~>* pfiber g
  := pequiv_pfiber p.

(** It's useful to see [pfib_cxfib] as a degenerate square. *)
Definition square_pfib_pequiv_cxfib
           {F X Y : pType} (i : F ->* X) (f : X ->* Y)
           `{IsExact oo F X Y i f}
  : Square i (pfib f) (pequiv_cxfib) (pequiv_pmap_idmap).
Proof.
  unfold Square.
  refine (pmap_postcompose_idmap _ @* _).
  symmetry; apply pfib_cxfib.
Defined.

(** The connecting maps for the long exact sequence of loop spaces, defined as an extension to a fiber sequence. *)
Definition connect_fiberseq {F X Y} (i : F ->* X) (f : X ->* Y)
           `{IsExact oo F X Y i f}
  : FiberSeq (loops Y) F X.
Proof.
  exists i.
  exact (((pfiber2_loops f) o*E (pequiv_pfiber (square_pfib_pequiv_cxfib i f)))^-1*).
Defined.

Definition connecting_map {F X Y} (i : F ->* X) (f : X ->* Y)
           `{IsExact oo F X Y i f}
  : loops Y ->* F
  := i_fiberseq (connect_fiberseq i f).

Global Instance isexact_connect_R {F X Y} (i : F ->* X) (f : X ->* Y)
       `{IsExact oo F X Y i f}
  : IsExact oo (loops_functor f) (connecting_map i f).
Proof.
  refine (isexact_squaric_i (Y := F) oo
          (pfib (pfib i)) (loops_functor f)
          (((loops_inv X) o*E
            (pfiber2_loops (pfib f)) o*E
           (pequiv_pfiber (square_pequiv_pfiber (square_pfib_pequiv_cxfib i f))))^-1*)
          (((pfiber2_loops f) o*E (pequiv_pfiber (square_pfib_pequiv_cxfib i f)))^-1*)
          _ (pfib i)).
  refine (vinverse 
            ((loops_inv X) o*E
             (pfiber2_loops (pfib f)) o*E
             (pequiv_pfiber (square_pequiv_pfiber (square_pfib_pequiv_cxfib i f))))
            ((pfiber2_loops f) o*E (pequiv_pfiber (square_pfib_pequiv_cxfib i f))) _).
  refine (vconcat (f03 := loops_inv X o* pfiber2_loops (pfib f))
                  (f01 := pequiv_pfiber (square_pequiv_pfiber (square_pfib_pequiv_cxfib i f)))
                  (f23 := pfiber2_loops f)
                  (f21 := pequiv_pfiber (square_pfib_pequiv_cxfib i f)) _ _).
  - exact (square_pequiv_pfiber (square_pequiv_pfiber (square_pfib_pequiv_cxfib i f))).
  - exact (pfiber2_loops_functor f).
Defined.


(** ** Long exact sequences *)

Record LongExactSequence (k : Modality) (N : SuccStr) : Type :=
{
  les_carrier : N -> pType;
  les_fn : forall n, les_carrier n.+1 ->* les_carrier n;
  les_isexact : forall n, IsExact k (les_fn n.+1) (les_fn n)
}.

Coercion les_carrier : LongExactSequence >-> Funclass.
Arguments les_fn {k N} S n : rename.
Global Existing Instance les_isexact.

(** Long exact sequences are preserved by truncation. *)
Definition trunc_les (k : trunc_index) {N : SuccStr}
           (S : LongExactSequence oo N)
  : LongExactSequence (Tr k) N
  := Build_LongExactSequence
       (Tr k) N (fun n => pTr k.+1 (S n))
       (fun n => ptr_functor k.+1 (les_fn S n)) _.


(** ** LES of loop spaces and homotopy groups *)

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
  { exact (connecting_map (iterated_loops_functor n i)
                          (iterated_loops_functor n f)). }
  all:exact _.
Defined.

(** And from that, a long exact sequence of homotopy groups (though for now it is just a sequence of pointed sets). *)
Definition Pi_les {F X Y : pType} (i : F ->* X) (f : X ->* Y)
           `{IsExact oo F X Y i f}
  : LongExactSequence (Tr (-1)) (N3)
  := trunc_les (-1) (loops_les i f).

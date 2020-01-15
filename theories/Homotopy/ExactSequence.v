Require Import Basics.
Require Import Types.
Require Import SuccessorStructure.
Require Import Pointed.
Require Import ReflectiveSubuniverse Modality Modalities.Identity.
Require Import Truncations.
Require Import Fibrations EquivalenceVarieties.

Open Scope pointed_scope.

(** * Exact sequences *)

(** The notion of exactness makes sense relative to any modality.  To state it in that level of generality would require module-type hackery.  But in practice we only want to apply it to the (-1)-truncation and to the identity modality.  Unfortunately none of the standard families of modalities includes both of those, but we can take a union of the truncation modalities with the identity modality. *)
Module TrId_Modalities :=  Modalities_FamUnion Truncation_Modalities Identity_Modalities.
Module Import TrIdM := Modalities_Theory TrId_Modalities.

(** Unfortunately this way we don't automatically inherit the useful shortcuts about truncation modalities, so we have to redefine some of them. *)
Global Instance issepfor_TrId (n : trunc_index) : IsSepFor (Tr n.+1) (Tr n).
Proof.
  intros A; split; intros; apply inO_tr_istrunc; exact _.
Defined.

(** A (short) complex is a pair of pointed maps whose composite is the zero map. *)
Class IsComplex {F X Y : pType} (f : X ->* Y) (i : F ->* X)
  := cx_const : f o* i ==* pConst.

Arguments cx_const {F X Y} f i {_}.

Definition cx_to_fiber {F X Y : pType} (f : X ->* Y) (i : F ->* X)
           `{IsComplex F X Y f i}
  : F ->* pfiber f.
Proof.
  srapply Build_pMap.
  - intros x; exact (i x ; cx_const _ _ x).
  - cbn. refine (path_sigma' _ (point_eq i) _).
    refine (transport_paths_Fl _ _ @ _).
    apply moveR_Vp.
    exact ((concat_p1 _)^ @ point_htpy (cx_const _ _)).
Defined.

(** Truncation preserves complexes. *)
Global Instance iscomplex_ptr (n : trunc_index)
       {F X Y : pType} (f : X ->* Y) (i : F ->* X) `{IsComplex F X Y f i}
  : IsComplex (ptr_functor n f) (ptr_functor n i).
Proof.
  refine ((ptr_functor_pmap_compose n i f)^* @* _).
  refine (_ @* ptr_functor_pconst n).
  apply ptr_functor_homotopy; assumption.
Defined.

(** A complex is n-exact if the induced map [cx_to_fiber] is n-connected.  *)
Class IsExact (n : Modality)
      {F X Y : pType} (f : X ->* Y) (i : F ->* X) `{IsComplex F X Y f i}
  := conn_map_isexact : IsConnMap n (cx_to_fiber f i).

Global Existing Instance conn_map_isexact.

(** When [n] is the identity modality, so that [cx_to_fiber] is an equivalence, we get simply a fiber sequence. *)
Global Instance isexact_oo_fiberseq
       {F X Y : pType} (f : X ->* Y) (i : F ->* X) `{IsComplex F X Y f i}
       `{IsEquiv F (pfiber f) (cx_to_fiber f i)}
  : IsExact oo f i.
Proof.
  intros z; serapply fcontr_isequiv.
Defined.

(** (n.+1)-truncation preserves n-exactness. *)
Definition isexact_ptr (n : trunc_index)
           {F X Y : pType} (f : X ->* Y) (i : F ->* X)
           `{IsComplex F X Y f i} `{!IsExact (Tr n) f i}
  : IsExact (Tr n) (ptr_functor n.+1 f) (ptr_functor n.+1 i).
Proof.
  simple notypeclasses refine
    (cancelR_conn_map (Tr n) (@tr n.+1 F) 
      (cx_to_fiber (ptr_functor n.+1 f) (ptr_functor n.+1 i))).
  { intros x; rapply isconnected_pred. }
  refine (conn_map_homotopic (Tr n) _ _ _
           (conn_map_compose (Tr n) (cx_to_fiber f i)
             (functor_hfiber (fun y => (to_O_natural (Tr n.+1) f y)^) (point Y)))).
  intros x; refine (path_sigma' _ 1 _); cbn.
  (* This is even simpler than it looks, because for truncations [to_O_natural n.+1 := 1], [to n.+1 := tr], and [cx_const := H]. *)
  exact (1 @@ (concat_p1 _)^).
Defined.

(** In particular, (n.+1)-truncation takes fiber sequences to n-exact ones. *)
Definition isexact_ptr' (n : trunc_index)
           {F X Y : pType} (f : X ->* Y) (i : F ->* X) `{IsExact oo F X Y f i}
  : IsExact (Tr n) (ptr_functor n.+1 f) (ptr_functor n.+1 i).
Proof.
  rapply isexact_ptr.
  intros z; apply isconnected_contr.
  exact (conn_map_isexact (f := f) (i := i) z).
Defined.

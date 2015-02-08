(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics.Overture HoTT.Basics.Trunc.
Require Import Modalities.Modality Comodalities.Comodality.

(** * Wrapping modalities *)

(** When comparing modalities and comodalities, it's useful to have module wrappers for single modalities. *)

Module Type ModalityM.
  Declare Module Os : Modalities.
  Parameter m : Os.Modality.
End ModalityM.

(** ** Modality subuniverses *)

(** Every modality gives rise to a subuniverse *)

Module Modal_Subuniverse (OM : ModalityM)
       (** forall *)
       (XM : TypeM)
  <: Subuniverse XM.
  (** I haven't thought about whether this assignment of universes is "correct"; I only know that without any universe annotations, it ends up being too polymorphic (4 universe parameters), and this way it works. *)
  Definition m : Type2@{j i}
    := OM.Os.In@{j i j} OM.m@{j i} XM.m@{j i}.
  Definition m_ishprop (fs : Funext) : IsHProp m
    := OM.Os.hprop_inO fs OM.m XM.m.
End Modal_Subuniverse.

(** Such subuniverses are, of course, automatically closed under finite limits. *)

Module Modal_Subuniverse_Limits (OM : ModalityM).
  Module InF (XM : TypeM) <: Subuniverse XM := Modal_Subuniverse OM XM.
  Module Import Os_Theory := Modalities_Theory OM.Os.

  Module isinF_unit_M : InF_Unit_M InF.
    Module InF_M := InF UnitM.
    Definition m : InF_M.m.
    Proof.
      unfold InF_M.m.
      (** We can't rely on typeclass inference, since we need to give universe annotations to reduce the polymorphism. *)
      apply Os_Theory.RSU.inO_unit@{j i j j}.
    Defined.
  End isinF_unit_M.

  Module isinF_prod_M
         (XM YM : TypeM)
         (isinF_XM : InM InF XM) (isinF_YM : InM InF YM)
  <: InF_Prod_M InF XM YM isinF_XM isinF_YM.
    (** Work around https://coq.inria.fr/bugs/show_bug.cgi?id=4003.  These should be judgmental equalities.  We make them functions rather than (say) propositional equalities, to avoid introducing extra universe parameters. *)
    Axiom isinF_XM_eq_admitted : isinF_XM.InF_M.m -> In OM.m XM.m.
    Axiom isinF_YM_eq_admitted : isinF_YM.InF_M.m -> In OM.m YM.m.
    (** Unfortunately, bug 4003 is nasty enough that these workaround axioms actually make Coq inconsistent.  But as long as we don't do stupid things, we should be fine. *)
    Module PM := ProdM XM YM.
    Module InF_M := InF PM.
    Definition m : InF_M.m.
    Proof.
      unfold InF_M.m.
      unfold PM.m.
      (** See remark above about typeclass inference and universe polymorphism. *)
      refine (@Os_Theory.RSU.inO_prod@{j i j j j j j j j}
                                     OM.m XM.m YM.m _ _).
      - apply isinF_XM_eq_admitted.
        exact (isinF_XM.m).
      - apply isinF_YM_eq_admitted.
        exact (isinF_YM.m).
    Defined.
  End isinF_prod_M.

End Modal_Subuniverse_Limits.

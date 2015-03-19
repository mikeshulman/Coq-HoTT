(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics HoTT.Types.Bool HoTT.Types.Prod.
Require Import hit.Truncations.
Require Import Modalities.Modality Comodalities.Comodality Comodalities.ModalityM.

(** * Shape *)

(** A shape situation consists of a modality and a comodality having the same subuniverse of types. *)

Module Shape_Theory (ShapeM : ModalityM).

  (** The modal types are called "discrete". *)
  Module Discrete <: Subuniverse := Modal_Subuniverse ShapeM.
  Module Import Discrete_Theory := Modalities_Theory ShapeM.Os.

  (** Discrete types are therefore closed under limits. *)
  Module Import Discrete_Limits := Modal_Subuniverse_Limits ShapeM.

  (** We suppose that the discrete types are also the comodal types for a comodality, by hypothesizing [Flat : Comodality Discrete]. *)

  (** ** Pieces have points *)

  (** We say that "pieces have points" if each induced map from [Flat X] to [Shape X] is surjective.  Lawvere calls this the "nullstellensatz"; Johnstone calls it "punctual local connectedness". *)
  Module Type Pieces_Have_Points
         (** forall *)
         (XM : TypeM) (FXM : Comodality Discrete XM).
    Parameter m : IsSurjection (to ShapeM.m XM.m o FXM.from).
  End Pieces_Have_Points.

  Module mM (Flat : Comodality Discrete).
    Module Import Flat_Theory := Comodality_Theory Discrete Flat.

    (** ** Closure properties *)

    (** Since the discrete types contain [Unit], they also contain [Bool] and [nat] and [S1]. *)
    Module Discrete_Bool <: InM Discrete BoolM  := isinF_Bool_M isinF_unit_M.
    Module Discrete_Nat <: InM Discrete NatM := isinF_Nat_M isinF_unit_M.
    Module Discrete_S1 <: InM Discrete S1M := isinF_S1_M isinF_unit_M.

    (** And since the discrete types are closed under products, the coreflector [Flat] preserves products and hprops. *)
    Module isequiv_Flat_prod_cmp_M
      := isequiv_F_prod_cmp_M isinF_prod_M.
    Module ishprop_Flat_hprop_M
      := ishprop_F_M isinF_prod_M.
    
    (** It follows that if pieces have points, then every hprop is discrete.  (Thanks to Zhen Lin for this argument.) *)
    Module discrete_hprop_M
           (ppM : Pieces_Have_Points)
           (XM : TypeM) (hpXM : IsHPropM XM)
           (Flat_XM : Comodality Discrete XM)
        <: InM Discrete XM.
      Module ppXM := ppM XM Flat_XM.
      Module Shape_XM <: TypeM.
        Definition m : Type2@{i j} := ShapeM.m@{i j} XM.m@{i j}.
      End Shape_XM.
      Module ishprop_shape_XM := ishprop_Flat_hprop_M XM hpXM Flat_XM.
      Module sM : FunctionM XM Flat_XM.
        Definition m : XM.m@{i j} -> Flat_XM.m@{i j}.
        Proof.
          intros x.
          assert (f := to@{i j i} ShapeM.m@{i j} XM.m@{i j} o Flat_XM.from@{i j}).
          assert (IsEquiv f).
          { (** We pose this explicitly, rather than relying on typeclass inference, to prevent unwanted universe parameters. *)
            pose proof (@ishprop_O_ishprop@{i j i i i}
                          ShapeM.m@{i j} XM.m@{i j} hpXM.m@{i j}).
            apply isequiv_iff_hprop; intros y.
            assert (z := @center _ (ppXM.m@{i j i i} y)).
            strip_truncations.
            exact (z.1). }
          apply (f^-1), to; assumption.
        Defined.
      End sM.
      Module HM : SectM XM Flat_XM sM Flat_XM.fromM.
        Definition m : Sect sM.m Flat_XM.from.
        Proof.
          intros x; apply path_ishprop.
        Defined.
      End HM.
      Module mM := inF_from_F_section_M XM Flat_XM sM HM.
      Include mM.
    End discrete_hprop_M.

  End mM.
End Shape_Theory.

(* -*- mode: coq; mode: visual-line -*-  *)
Require Import HoTT.Basics HoTT.Types.
Require Import UnivalenceImpliesFunext.
Require Import Modalities.Modality.
Require Import Truncations.
Require Import Spaces.Finite Spaces.Nat.
Require Import Colimits.Quotient.
Require Import Algebra.ooGroup.
Import TrM.

(** * Finite Groups *)

Local Open Scope path_scope.

(** ** Lagrange's theorem *)

(** We first formulate Lagrange's theorem in terms of the quotient by a subgroup. *)
Section Lagrange.
  Context `{ua : Univalence}.
  Context (G H : ooGroup) (incl : ooGroupHom H G) `{IsEmbedding incl}.
  Context `{Finite G} `{Finite H}.

  Global Instance decidable_in_coset (g1 g2 : G)
  : Decidable (in_coset incl g1 g2).
  Proof.
    by apply detachable_image_finite.
  Defined.

  Global Instance finite_cosets : Finite (cosets incl).
  Proof.
    exact _.
  Defined.

  Definition lagrange : fcard G = (fcard (cosets incl) * fcard H)%nat.
  Proof.
    refine (fcard_quotient (in_coset incl) @ _ @ finplus_const (cosets incl) (fcard H)).
    apply ap, path_arrow; intros z; simpl.
    refine (Trunc_rec _ (center (merely (hfiber (class_of (in_coset incl)) z)))).
    intros [g p]; rewrite <- p; exact (fcard_equiv' (equiv_coset_subgroup incl g)).
  Qed.

End Lagrange.

(** Then we derive from this a version about surjective group homomorphisms. *)
Section Surjections.

  Context `{fs : Funext}.
  Context {G H : ooGroup} (sur : ooGroupHom G H) `{IsSurjection sur}.

  (** The real [kernel] should be be another [ooGroup], of course. *)
  Definition kernel_set := hfiber sur 1.

  (** This ought to be true for any oo-groups, without a truncation assumption. *)
  Definition merely_equiv_fiber_kernel `{IsHSet H} (h : H)
  : merely (hfiber sur h <~> kernel_set).
  Proof.
    assert (x := center (merely (hfiber sur h))).
    strip_truncations; destruct x as [g p]; apply tr; unfold kernel_set.
    destruct p.
    simple refine (equiv_adjointify _ _ _ _).
    - intros [g' p']. exists (g @ g'^).
      refine (grouphom_pp _ _ _ @ _).
      refine ((p'^ @@ grouphom_V _ _) @ _).
      apply concat_pV.
    - intros [g' p']. exists (g'^ @ g).
      refine (grouphom_pp _ _ _ @ _).
      refine (((grouphom_V _ _ @ inverse2 p') @@ 1) @ concat_1p _).
    - intros [g' p']. apply path_sigma_hprop; simpl.
      rewrite inv_pp, concat_p_Vp, inv_V; reflexivity.
    - intros [g' p']. apply path_sigma_hprop; simpl.
      rewrite inv_pp, inv_V, concat_pV_p; reflexivity.
  Qed.

  Context `{Finite G} `{Finite H}.

  Definition fcard_fiber_kernel (h : H)
  : fcard (hfiber sur h) = fcard kernel_set.
  Proof.
    assert (e := merely_equiv_fiber_kernel h).
    strip_truncations.
    exact (fcard_equiv' e).
  Defined.

  Definition fcard_group_surj
  : fcard G = (fcard H * fcard kernel_set)%nat.
  Proof.
    refine (fcard_domain sur @ _ @ finplus_const H (fcard kernel_set)).
    apply ap, path_arrow; intros h; apply fcard_fiber_kernel.
  Defined.

End Surjections.

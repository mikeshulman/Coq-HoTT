Require Import Basics.
Require Import Types.
Require Import Algebra.Group.
Require Import Algebra.AbelianGroup.
Require Import Algebra.Subgroup.
Require Import Algebra.GradedAbGroup.
Require Import WildCat.
Require Import Algebra.Kernel.
Require Import Algebra.Image.
Require Import Algebra.Homology.

Section ExactCouple.

  Context `{Univalence} {G : AbGroup}.

  Class IsGrExact {A B C : GradedGroup G} (f : A $-> B) (g : B $-> C) := {
    graded_isexact : forall x,
      grp_kernel (gh_component g x) $<~> grp_image (gh_component_prev f x);
  }.

  Record ExactCouple := {
    D : GradedGroup G;
    E : GradedGroup G;
    i : D $-> D;
    j : D $-> E;
    k : E $-> D;
    ec1 : IsGrExact i j;
    ec2 : IsGrExact j k;
    ec3 : IsGrExact k i;
  }.

  Definition GrImage {A B : GradedGroup G} (f : A $-> B) : GradedGroup G
    := fun x => grp_image (gh_component_prev f x).

  Definition gh_image_pr1 {A B : GradedGroup G} (f : A $-> B) : GrImage f $-> B.
  Proof.
    serapply Build_GradedHomomorphism'.
    1: reflexivity.
    { intro x.
      symmetry.
      apply right_identity. }
    cbn; intros x y [].
    apply grp_image_pr1.
  Defined.

  Definition gh_image_in {A B : GradedGroup G} (f : A $-> B) : A $-> GrImage f.
  Proof.
    serapply Build_GradedHomomorphism'.
    1: exact (deg f).
    1: apply deg_eq.
    intros x y p.
    unfold GrImage.
    apply moveL_equiv_V in p.
    destruct p^.
(*     apply grp_image. *)
    apply (grp_image_in (gh_component_prev f y)).
  Defined.

  Definition path_gh_image_in_prev {A B : GradedGroup G} (f : A $-> B) (x : G)
    : gh_component_prev (gh_image_in f) x = grp_image_in (gh_component_prev f x).
  Proof.
    simpl.
  Admitted.

  Definition DerivedCouple : ExactCouple -> ExactCouple.
  Proof.
    intros [D E i j k].
    simple notypeclasses refine (Build_ExactCouple _ _ _ _ _ _ _ _).
    (** D' *)
    1: exact (GrImage i).
    (** E' *)
    1: exact (Homology k j).
    (** i' *)
    1: exact (gh_image_in i $o gh_image_pr1 i).
    (** j' *)
    (** Difficult *)
    (** k' *)
    (** Difficult *)
    (** Show that everything is exact... *)
  Admitted.

End ExactCouple.
Require Import Basics Types.
Require Import Groups AbGroups.

Local Open Scope mc_add_scope.

(* A G-graded abelian group is simply a family of abelina groups over G *)
Definition GradedGroup (G : AbGroup) := G -> AbGroup.

Record GradedHomomorphism {G : AbGroup} (M M' : GradedGroup G)
  := Build_GradedHomomorphism'
{
  deg : G <~> G;
  deg_eq : forall g, deg g = g + deg mon_unit;
  homo {x y : G} : deg x = y -> GroupHomomorphism (M x) (M' y);
}.

Arguments deg {_ _ _}.
Arguments deg_eq {_ _ _}.

Definition Build_GradedHomomorphism {G : AbGroup}
  {M M' : GradedGroup G} (degree : G)
  (hom : forall x, GroupHomomorphism (M x) (M' (x + degree)))
  : @GradedHomomorphism G M M'.
Proof.
  srapply Build_GradedHomomorphism'.
  { apply right_mult_equiv.
    exact degree. }
  { intro x; cbn.
    apply ap.
    symmetry.
    apply left_identity. }
  intros x y [].
  apply hom.
Defined.

Definition gh_component {G M M'} (f : @GradedHomomorphism G M M')
  (g : G) : GroupHomomorphism (M g) (M' (deg f g))
  := homo _ _ f idpath.

Definition gh_compose {G M M' M''}
  (g : GradedHomomorphism M' M'')
  (f : @GradedHomomorphism G M M')
  : GradedHomomorphism M M''.
Proof.
  srapply Build_GradedHomomorphism'.
  + exact (deg g oE deg f).
  + intro x.
    simpl.
    rewrite 2 deg_eq.
    symmetry.
    rewrite 2 deg_eq.
    rewrite simple_associativity.
    reflexivity.
  + cbn; intros x y p.
    snrapply Build_GroupHomomorphism.
    { intro z.
      srapply (homo _ _ g).
      3: srapply (homo _ _ f).
      5: apply z.
      2: apply p.
      reflexivity. }
    intros a b.
    by rewrite 2 grp_homo_op.
Defined.

Definition gh_zero {G M M'}
  : @GradedHomomorphism G M M'.
Proof.
  srapply Build_GradedHomomorphism.
  1: exact mon_unit.
  intro x.
  snrapply Build_GroupHomomorphism.
  { intro.
    apply mon_unit. }
  intros _ _.
  symmetry.
  apply left_identity.
Defined.

Definition gh_component_prev {G M M'} (f : @GradedHomomorphism G M M') (g : G)
  : GroupHomomorphism (M ((deg f)^-1 g)) (M' g).
Proof.
  apply (homo _ _ f).
  apply eisretr.
Defined.

Require Import WildCat.

Section WildCat.

  Context {G : AbGroup}.

  Global Instance isgraph_gradedgroups : IsGraph (GradedGroup G)
    := Build_IsGraph (GradedGroup G) GradedHomomorphism.

  Global Instance is01cat_gradedgroups : Is01Cat (GradedGroup G).
  Proof.
    srapply Build_Is01Cat.
    + intros x.
      srapply Build_GradedHomomorphism'.
      1: reflexivity.
      { intro g.
        symmetry.
        apply right_identity. }
      { intros ? ? [].
        apply grp_homo_id. }
    + intros ???; exact gh_compose.
  Defined.

End WildCat.





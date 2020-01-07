(** * Definition of a [PreCategory] *)
Require Export Overture Basics.Notations.
Require Export Basics.WildCat.

Set Universe Polymorphism.
Set Implicit Arguments.
Generalizable All Variables.
Set Asymmetric Patterns.

Declare Scope morphism_scope.
Declare Scope category_scope.
Declare Scope object_scope.

Delimit Scope morphism_scope with morphism.
Delimit Scope category_scope with category.
Delimit Scope object_scope with object.

Local Open Scope morphism_scope.

(** Quoting the HoTT Book: *)
(** Definition 9.1.1. A precategory [A] consists of the following.

    (i) A type [A₀] of objects. We write [a : A] for [a : A₀].

    (ii) For each [a, b : A], a set [hom_A(a, b)] of arrows or morphisms.

    (iii) For each [a : A], a morphism [1ₐ : hom_A(a, a)].

    (iv) For each [a, b, c : A], a function

         [hom_A(b, c) → hom_A(a, b) → hom_A(a, c)]

         denoted infix by [g ↦ f ↦ g ∘ f] , or sometimes simply by [g f].

    (v) For each [a, b : A] and [f : hom_A(a, b)], we have [f = 1_b ∘
        f] and [f = f ∘ 1ₐ].

    (vi) For each [a, b, c, d : A] and [f : hom_A(a, b)], [g :
         hom_A(b, c)], [h : hom_A(c,d)], we have [h ∘ (g ∘ f) = (h ∘
         g) ∘ f]. *)
(** In addition to these laws, we ask for a few redundant laws to give
    us more judgmental equalities.  For example, since [(p^)^ ≢ p] for
    paths [p], we ask for the symmetrized version of the associativity
    law, so we can swap them when we take the dual. *)

(** This is not without it's problems, as the fields below are no
    longer 1-step projections certain proof searches and tactics fail.
    *)
Record PreCategory :=
  Build_PreCategoryW {
      object :> Type;
      zc1c : Is0Coh1Cat object;
      strength : @Is1Coh1Cat_Strong object zc1c as0Coh2CatPath;
      trunc_morphism : forall s d, IsHSet (s $-> d) }.

Global Existing Instance strength.
Global Existing Instance zc1c.
Global Existing Instance trunc_morphism.

Definition morphism (p : PreCategory) (s d : p) :=  s $-> d.

Definition identity (p : PreCategory) (s : p) := Id s.

Definition compose (p : PreCategory) (s d d' : p)
           (f : d $-> d') (g : s $-> d) :=  f $o g.

Bind Scope category_scope with PreCategory.
Bind Scope object_scope with object.
Bind Scope morphism_scope with morphism.

(** We want eta-expanded primitive projections to [simpl] away. *)
Arguments object !C%category / : rename.
Arguments morphism !C%category / s d : rename.
Arguments identity {!C%category} / x%object : rename.
Arguments compose {!C%category} / {s d d'}%object (m1 m2)%morphism : rename.

Local Infix "o" := compose : morphism_scope.
Local Notation "x --> y" := (morphism _ x y) : type_scope.
Local Notation "1" := (identity _) : morphism_scope.

Definition associativity (p : PreCategory) (x1 x2 x3 x4 : p)
           (m1 : x1 --> x2) (m2 : x2 --> x3) (m3 : x3 --> x4) :
  (m3 o m2) o m1 = m3 o (m2 o m1).
Proof.
  rapply (@cat_assoc p _ as0Coh2CatPath).
Defined.

Definition associativity_sym (p : PreCategory) (x1 x2 x3 x4 : p)
           (m1 : x1 --> x2) (m2 : x2 --> x3) (m3 : x3 --> x4) :
  m3 o (m2 o m1) = (m3 o m2) o m1.
Proof.
  rapply (@cat_assoc_opp _ _ as0Coh2CatPath).
Defined.

Definition left_identity (p : PreCategory) (a b : p) (f : a --> b)
  : 1 o f = f.
Proof.
  rapply (@cat_idl p _ as0Coh2CatPath).
Defined.

Definition right_identity (p : PreCategory) (a b : p) (f : a --> b)
  : f o 1 = f.
Proof.
  rapply (@cat_idr p _ as0Coh2CatPath).
Defined.

(** Ask for the double-identity version so that [InitialTerminalCategory.Functors.from_terminal Cᵒᵖ X] and [(InitialTerminalCategory.Functors.from_terminal C X)ᵒᵖ] are convertible. *)
Definition identity_identity (p : PreCategory) (x : p)
  : identity x o identity x = identity x.
Proof.
  rapply (@cat_idlr p _ as0Coh2CatPath).
Defined.

Definition Build_PreCategory' (object : Type)
           (morphism : object -> object -> Type)
           (identity : forall (x : object), morphism x x)
           (compose : forall (s d d' : object),
               morphism d d' ->
               morphism s d -> morphism s d')
           (associativity : forall (x1 x2 x3 x4 : object)
                              (m1 : morphism x1 x2)
                              (m2 : morphism x2 x3)
                              (m3 : morphism x3 x4),
               compose x1 x2 x4 (compose x2 x3 x4 m3 m2) m1
               = compose x1 x3 x4 m3 (compose x1 x2 x3 m2 m1))
           (associativy_sym : forall (x1 x2 x3 x4 : object)
                                (m1 : morphism x1 x2)
                                (m2 : morphism x2 x3)
                                (m3 : morphism x3 x4),
               compose x1 x3 x4 m3 (compose x1 x2 x3 m2 m1) =
               compose x1 x2 x4 (compose x2 x3 x4 m3 m2) m1)
       (left_identity : forall (a b : object) (f : morphism a b),
           compose a b b (identity b) f = f)
       (right_identity : forall (a b : object) (f : morphism a b),
           compose a a b f (identity a) = f)
       (identity_identity : forall x : object,
           compose x x x (identity x) (identity x) =
           identity x)
       (trunc_morphism : forall s d : object,
           IsHSet (morphism s d)) : PreCategory.
Proof.
  srapply (@Build_PreCategoryW object).
  - exact (Build_Is0Coh1Cat object morphism identity compose).
  - srapply Build_Is1Coh1Cat_Strong.
    + apply associativity.
    + apply left_identity.
    + apply right_identity.
  - apply trunc_morphism.
Defined.

(** Define a convenience wrapper for building a precategory without
    specifying the redundant proofs. *)
Definition Build_PreCategory
           object morphism identity compose
           associativity left_identity right_identity
  := @Build_PreCategory'
       object
       morphism
       identity
       compose
       associativity
       (fun _ _ _ _ _ _ _ => symmetry _ _ (associativity _ _ _ _ _ _ _))
       left_identity
       right_identity
       (fun _ => left_identity _ _ _).

(** create a hint db for all category theory things *)
Create HintDb category discriminated.
(** create a hint db for morphisms in categories *)
Create HintDb morphism discriminated.

Hint Resolve @left_identity @right_identity @associativity : category morphism.
Hint Rewrite @left_identity @right_identity : category.
Hint Rewrite @left_identity @right_identity : morphism.

(** ** Simple laws about the identity morphism *)
Section identity_unique.
  Variable C : PreCategory.

  (** The identity morphism is unique. *)
  Lemma identity_unique (id0 id1 : forall x, morphism C x x)
        (id1_left : forall s d (m : morphism C s d), id1 _ o m = m)
        (id0_right : forall s d (m : morphism C s d), m o id0 _ = m)
  : id0 == id1.
  Proof.
    intro.
    etransitivity;
      [ symmetry; apply id1_left
      | apply id0_right ].
  Qed.

  (** Anything equal to the identity acts like it.  This is obvious,
      but useful as a helper lemma for automation. *)
  Definition concat_left_identity s d (m : morphism C s d) i
  : i = 1 -> i o m = m
    := fun H => (ap10 (ap _ H) _ @ left_identity _ _ _ m)%path.

  Definition concat_right_identity s d (m : morphism C s d) i
  : i = 1 -> m o i = m
    := fun H => (ap _ H @ right_identity _ _ _ m)%path.
End identity_unique.

(** Make a separate module for Notations, which can be exported/imported separately. *)
Module Export CategoryCoreNotations.
  Infix "o" := compose : morphism_scope.
  (** Perhaps we should consider making this notation more global. *)
  (** Perhaps we should pre-reserve all of the notations. *)
  Local Notation "x --> y" := (@morphism _ x y) : type_scope.
  Local Notation "x --> y" := (morphism _ x y) : type_scope.
  Notation "1" := (identity _) : morphism_scope.
End CategoryCoreNotations.

(** We have a tactic for trying to run a tactic after associating morphisms either all the way to the left, or all the way to the right *)
Tactic Notation "try_associativity_quick" tactic(tac) :=
  first [ rewrite <- ?associativity; tac
        | rewrite -> ?associativity; tac ].

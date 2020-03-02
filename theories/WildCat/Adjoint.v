Require Import Basics.
Require Import WildCat.Core.
Require Import WildCat.Comma.
Require Import WildCat.TwoOneCat.

(** Having a left adjoint *)
Definition HasLeftAdjoint {A B : Type} (F : A -> B)
  `{Is1Functor A B F, !Is21Cat B}
  := forall (x : B), HasInitial (Comma (@const A B x) F).

(** Having a right adjoint *)
Definition HasRightAdjoint {A B : Type} (F : A -> B)
  `{Is1Functor A B F, !Is21Cat B}
  := forall (x : B), HasInitial (Comma F (@const A B x) ).






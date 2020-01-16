(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Import WildCat.

Definition IsInitial {A : Type} `{Is0Coh2Cat A} (x : A)
  := forall (y : A), {f : x $-> y & forall g, f $== g}.

Existing Class IsInitial.



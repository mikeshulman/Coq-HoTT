(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Import WildCat.Core.

Definition IsInitial {A : Type} `{Is1Cat A} (x : A)
  := forall (y : A), {f : x $-> y & forall g, g $== f}.

Existing Class IsInitial.



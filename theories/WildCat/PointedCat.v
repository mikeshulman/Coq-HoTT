Require Import Basics Types.
Require Import WildCat.Core.
Require Import WildCat.Initial.


Class IsPointedCat (A : Type) `{Is1Cat A} := {
  zero_object : A;
  isinitial_zero_object : IsInitial zero_object;
  isterminal_zero_object : IsTerminal zero_object;
}.

Definition zero_morphism {A : Type} `{IsPointedCat A} {a b : A} : a $-> b
  := (isinitial_zero_object b).1 $o (isterminal_zero_object a).1.

Require Import Basics Types.
Require Import WildCat.Core.

Class IsPointedCat (A : Type) `{Is1Cat A} := {
  zero_object : A;
  isinitial_zero_object : IsInitial zero_object;
  isterminal_zero_object : IsTerminal zero_object;
}.

Definition zero_morphism {A : Type} `{IsPointedCat A} {a b : A} : a $-> b
  := (isinitial_zero_object b).1 $o (isterminal_zero_object a).1.

Declare Scope pointedcat_scope.
Local Open Scope pointedcat_scope.

Notation "1" := zero_object : pointedcat_scope.
Notation "0" := zero_morphism : pointedcat_scope.

Section ZeroLaws.

  Context {A : Type} `{IsPointedCat A} {a b c : A}
    (f : a $-> b) (g : b $-> c).

  Local Arguments zero_morphism {_ _ _ _} _ _.

  Definition pc_zero_source (h : 1 $-> a) : h $== 0
    := (isinitial_zero_object a).2 h
      $@ ((isinitial_zero_object a).2 0)^$.

  Definition pc_zero_target (h : a $-> 1) : h $== 0
    := (isterminal_zero_object a).2 h
      $@ ((isterminal_zero_object a).2 0)^$.

  Definition comp_f0 : g $o 0 $== zero_morphism a c.
  Proof.
    refine ((cat_assoc _ _ _)^$ $@ _).
    apply cat_prewhisker.
    apply (isinitial_zero_object c).2.
  Defined.

  Definition comp_0f : 0 $o f $== zero_morphism a c.
  Proof.
    refine (cat_assoc _ _ _ $@ _).
    apply cat_postwhisker.
    apply (isterminal_zero_object a).2.
  Defined.

End ZeroLaws.


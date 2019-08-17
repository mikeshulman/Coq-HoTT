Require Import Basics.
Require Import Types.
Require Import HIT.Truncations.
Require Import HIT.Suspension.
Require Import HIT.SpanPushout.
Require Import HIT.Connectedness.
Require Import HIT.Join.
Require Import GBM.

(** ** The classical Blakers-Massey Theorem *)

Import TrM.
Module Import BlakersMassey := GenBlakersMassey Truncation_RSUs.

Instance blakers_massey `{Univalence} (m n : trunc_index)
     {X Y : Type} (Q : X -> Y -> Type)
     `{forall y, IsConnected m.+1 { x : X & Q x y } }
     `{forall x, IsConnected n.+1 { y : Y & Q x y } }
     (x : X) (y : Y)
  : IsConnMap (m +2+ n) (@sglue X Y Q x y).
Proof.
  intros r.
  srefine (contr_code_inhab Q (m +2+ n) _ x
                            (merely_isconnected n _) (spushr Q y) r).
  intros x1 x3 y2 y4 q12 q32 q34; apply isconnected_join; exact _.
Defined.
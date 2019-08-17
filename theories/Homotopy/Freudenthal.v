Require Import Basics.
Require Import Types.
Require Import HIT.Truncations.
Require Import HIT.Suspension.
Require Import HIT.Pushout.
Require Import HIT.SpanPushout.
Require Import BlakersMassey.

Import TrM.

(** ** The Freudenthal Suspension Theorem *)

Instance freudenthal `{Univalence} (n : trunc_index)
  (X : Type) `{IsConnected n.+1 X} : IsConnMap (n +2+ n) (@merid X).
Proof.
  pose (blakers_massey n n (fun (u v:Unit) => X) tt tt).
  (* The only real work here is to relate the two pushouts, as one is a naive pushout and the other is a span-pushout. *)
  pose (f := equiv_pushout (equiv_contr_sigma (fun _ : Unit * Unit => X))^-1
                           (equiv_idmap Unit) (equiv_idmap Unit)
                           (fun x : X => idpath) (fun x : X => idpath)
        : Susp X <~> spushout (fun (u v:Unit) => X)).
  srefine (@cancelR_equiv_conn_map (n +2+ n) _ _ _ _
             (equiv_ap' f North South)
             (@conn_map_homotopic _ _ _ _ _ _
               (blakers_massey n n (fun (u v:Unit) => X) tt tt))).
  intros x.
  refine (_ @ (equiv_pushout_pp
                 (equiv_contr_sigma (fun _ : Unit * Unit => X))^-1
                 (equiv_idmap Unit) (equiv_idmap Unit)
                 (fun x : X => idpath) (fun x : X => idpath) x)^).
  exact ((concat_p1 _ @ concat_1p _)^).
Defined.
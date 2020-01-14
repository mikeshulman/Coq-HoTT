Require Import Basics.
Require Import SuccessorStructure.
Require Import Spaces.Finite.
Require Import Pointed.
Require Import Homotopy.HomotopyGroup.
Require Import Truncations.

Local Open Scope succ_scope.
Local Open Scope pointed_scope.

Local Notation "'0'" := (inl (inl (inr tt))).
Local Notation "'1'" := (inl (inr tt)).
Local Notation "'2'" := (inr tt).

Definition homotopy_groups {X Y : pType} (f : X ->* Y) (n : N3) : pType :=
  match n with
  | (n, inl (inl (inl x))) => Build_pType Unit tt (* inaccessible case *)
  | (n, 0) => Pi n Y
  | (n, 1) => Pi n X
  | (n, 2) => Pi n (pfiber f)
  end.

(* A pointed version pi_loops. *)
Definition pi_loops_pointed n X : Pi n.+1 X <~>* Pi n (loops X).
Proof.
  apply (Build_pEquiv' (pi_loops n X)).
  destruct n. 
  1: reflexivity.
  exact (ap tr (point_eq (unfold_iterated_loops' n.+1 X))).
Defined.

Definition homotopy_groups_hom {X Y : pType} (f : X ->* Y) (n : N3) : 
  homotopy_groups f (succ n) ->* homotopy_groups f n.
Proof.
  refine
    match n with
    | (n, inl (inl (inl x))) => _ (* inaccessible case *)
    | (n, 0) => pi_functor n f
    | (n, 1) => pi_functor n (pfib f)
    | (n, 2) => _
    end.
  + destruct x.
  + refine (_ o* pi_loops_pointed n Y). 
    refine (pi_functor n _).
    refine (pfib (pfib f) o* (pfiber2_loops f) ^-1* ).
Defined.
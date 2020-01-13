Require Import Basics.
Require Import Types.
Require Import Spaces.Int.
Require Import Spaces.Nat.
Require Import Spaces.Finite.

(** * Successor Structures. *)

(** A successor structure is just a type with a endofunctor on it, called 'successor'. 
  Typical examples include either the integers or natural numbers with the successor (or predecessor) operation. *)

Record SuccStr : Type := {
   carrier :> Type;
   succ : carrier -> carrier }.

Declare Scope succ_scope.
Local Open Scope succ_scope.
Delimit Scope succ_scope with succ.
Arguments succ {_} _.

Definition IntSucc : SuccStr := Build_SuccStr Int int_succ.
Definition NatSucc : SuccStr := Build_SuccStr nat Nat.succ.

Definition StratifiedType (N : SuccStr) (n : nat) : Type := N * Fin n.

Definition stratified_succ (N : SuccStr) (n : nat) (x : StratifiedType N n) : StratifiedType N n.
Proof.
  constructor.
  + induction n.
    - induction (snd x).
    - destruct (dec (snd x = inr tt)).
      * exact (succ (fst x)).
      * exact (fst x).
  + exact (cyclic_succ (snd x)).
Defined.

Definition Stratified (N : SuccStr) (n : nat) : SuccStr := Build_SuccStr (StratifiedType N n) (stratified_succ N n).

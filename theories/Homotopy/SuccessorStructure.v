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
Local Open Scope nat_scope.
Local Open Scope succ_scope.
Delimit Scope succ_scope with succ.
Arguments succ {_} _.

Notation "x .+1" := (succ x) : succ_scope.

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

Fixpoint succ_str_add {N : SuccStr} (n : N) (k : nat) : N :=
  match k with
  | O   => n
  | S k => (succ_str_add n k).+1
  end.

Infix "+" := succ_str_add : succ_scope.

Definition succ_str_add_succ {N : SuccStr} (n : N) (k : nat) : (n + k.+1) = n.+1 + k.
Proof.
  induction k.
  + reflexivity.
  + exact (ap succ IHk).
Defined.
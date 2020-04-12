(*
Given a sequence of LES's, we want to splice them together.
... -> G_{1,k+1} -> G_{1,k} -> ... -> G_{1,1} -> G_{1,0}
... -> G_{2,k+1} -> G_{2,k} -> ... -> G_{2,1} -> G_{2,0}
...
... -> G_{n,k+1} -> G_{n,k} -> ... -> G_{n,1} -> G_{n,0}
...

If we have equivalences:
G_{n,m) = G_{n+1,m+k}
G_{n,m+1) = G_{n+1,m+k+1}
such that the evident squares commute, we can obtain a single sequence

 ... -> G_{n,m} -> G_{n+1,m+k-1} -> ... -> G_{n+1,m} -> G_{n+2,m+k-1} -> ...

However, in this formalization, we will only do this for k = 3, because we get more definitional
equalities in this specific case than in the general case. The reason is that we need to check
whether a term `x : Fin (k.+1)` represents `k`. If we do this in general using
if x = k then ... else ...
we don't get definitionally that x = k and the successor of x is 0, which means that when defining
maps G_{n,m} -> G_{n+1,m+k-1} we need to transport along those paths, which is annoying.

So far, the splicing seems to be only needed for k = 3, so it seems to be sufficient.
*)

Require Import Basics.
Require Import Spaces.Finite.
Require Import Homotopy.ExactSequence Homotopy.SuccessorStructure.
Require Import ReflectiveSubuniverse Modality Modalities.Identity.
Require Import Pointed.
Require Import WildCat.
(* Require Import  . *)


Local Open Scope succ_scope.

Definition Stratified_succ_max {N : SuccStr} {n : nat} (x : Stratified N (n.+1)) (p : snd x = inr tt)
  : x .+1 = ((fst x) .+1, fin_zero).
Proof.
  simpl. unfold stratified_succ. simpl.
  rewrite p. reflexivity.
Defined.

Local Notation "'0'" := (inl (inl (inr tt))).
Local Notation "'1'" := (inl (inr tt)).
Local Notation "'2'" := (inr tt).

Definition splice_type {k : Modality} {N M : SuccStr} (G : N -> LongExactSequence k M) (m : M)
  (x : Stratified N 3) : pType :=
  G (fst x) (m + nat_fin 3 (snd x)).

Definition splice_map {k : Modality} {N M : SuccStr} (G : N -> LongExactSequence k M) (m : M)
  (e0 : forall n, G n.+1 m <~>* G n (m + 3)) (x : Stratified N 3)
  : splice_type G m x.+1 ->* splice_type G m x :=
  match x with
  | (n, inl (inl (inl x))) => Empty_rec _ x
  | (n, 0) => les_fn (G n) m
  | (n, 1) => les_fn (G n) m.+1
  | (n, 2) => les_fn (G n) m.+1.+1 o* e0 n
  end.

Definition splice {k : Modality} {N M : SuccStr} (G : N -> LongExactSequence k M) (m : M)
  (e0 : forall n, G n.+1 m <~>* G n (m + 3)) 
  (e1 : forall n, G n.+1 m.+1 <~>* G n (m + 4))
  (p : forall n, Square (les_fn (G n.+1) m) (les_fn (G n) (m + 3)) (e1 n) (e0 n))
  : LongExactSequence k (Stratified N 3).
Proof.
  srapply Build_LongExactSequence.
  1: exact (splice_type G m).
  1: exact (splice_map G m e0).
  intros (n&[[[[]|[]]|[]]|[]]).
  { exact (les_isexact _ _ (G n) m). }
  { srapply (isexact_square_if (H := les_isexact k _ (G n) (m + 1)) k _ _ _ _ _).
    2,3: apply pequiv_pmap_idmap.
    3: exact vrfl.
    2: exact (cat_idl _). }
  { srapply (isexact_square_if (H := les_isexact k _ (G n) (m + 2)) k _ _ _ _ _). 
    3: apply pequiv_pmap_idmap.
    3: exact (p n).
    exact (cat_idl _). }
Defined.
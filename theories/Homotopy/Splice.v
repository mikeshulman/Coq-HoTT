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

However, in this formalization, we will only do this for k = 3, because we get moreDefinitional
equalities in this specific case than in the general case. The reason is that we need to check
whether a term `x : fin (succ k)` represents `k`. If we do this in general using
if x = k then ... else ...
we don't getDefinitionally that x = k and the successor of x is 0, which means that when defining
maps G_{n,m} -> G_{n+1,m+k-1} we need to transport along those paths, which is annoying.

So far, the splicing seems to be only needed for k = 3, so it seems to be sufficient.

*)

Require Import Basics.
Require Import Spaces.Finite.
Require Import Homotopy.ExactSequence Homotopy.SuccessorStructure.
Require Import ReflectiveSubuniverse Modality Modalities.Identity.
Require Import Pointed.Core.
Require Import WildCat.
(* Require Import  . *)


Local Open Scope succ_scope.

Definition Stratified_succ_max {N : SuccStr} {n : nat} (x : Stratified N (n.+1)) (p : snd x = inr tt)
  : x .+1 = ((fst x) .+1, fin_zero _).
Proof.
  simpl. unfold stratified_succ. simpl.
  rewrite p. reflexivity.
Defined.

Module Import TrIdM := Modalities_Theory TrId_Modalities. (* Am I doing this right? *)

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
  : LongExactSequence k (Stratified N 2).
Admitted.
(*
Definition is_chain_complex_splice_map {N M : succ_str} (G : N -> chain_complex M) (m : M)
  (e0 : forall n, G (S n) m <~>* G n (m +' 3)) (e1 : forall n, G (S n) (S m) <~>* G n (S (m +' 3)))
  (p : forall n, e0 n o* cc_to_fn (G (S n)) m == cc_to_fn (G n) (m +' 3) o* e1 n) :
  forall (x : stratified N 2) (y : splice_type G m (S (S x))),
  splice_map G m e0 x (splice_map G m e0 (S x) y) = pt
  | (n, fin.mk 0 H) y .  cc_is_chain_complex (G n) m y
  | (n, fin.mk 1 H) y .  cc_is_chain_complex (G n) (S m) (e0 n y)
  | (n, fin.mk 2 H) y .  ap (cc_to_fn (G n) (S (S m))) (p n y) @
  cc_is_chain_complex (G n) (S (S m)) (e1 n y)
  | (n, fin.mk (k+3) H) y . begin exfalso, apply lt_le_antisymm H, apply le_add_left end.


Definition is_exact_splice {N M : succ_str} (G : N -> chain_complex M) (m : M)
  (e0 : forall n, G (S n) m <~>* G n (m +' 3)) (e1 : forall n, G (S n) (S m) <~>* G n (S (m +' 3)))
  (p : forall n, e0 n o* cc_to_fn (G (S n)) m == cc_to_fn (G n) (m +' 3) o* e1 n)
  (H2 : forall n, is_exact (G n)) : forall (x : stratified N 2), is_exact_at (splice G m e0 e1 p) x
  | (n, fin.mk 0 H) .  H2 n m
  | (n, fin.mk 1 H) . begin intro y q, induction H2 n (S m)  y   q  with x r,
  apply image.mk ((e0 n)^-1ᵉ x),
  exact ap (pmap.to_fun (cc_to_fn (G n) (S (S m)))) (to_right_inv (e0 n) x) @ r end
  | (n, fin.mk 2 H).
Proof. intro y q, induction H2 n (S (S m))  e0 n y   q  with x r,
  apply image.mk ((e1 n)^-1ᵉ x),
  refine _ @ to_left_inv (e0 n) y, refine _ @ ap (e0 n)^-1ᵉ r, apply @eq_inv_of_eq _ _ (e0 n),
  refine p n ((e1 n)^-1ᵉ x) @ _, apply ap (cc_to_fn (G n) (m +' 3)), exact to_right_inv (e1 n) x
Defined.
  | (n, fin.mk (k+3) H) . begin exfalso, apply lt_le_antisymm H, apply le_add_left end.
Defined. chain_complex
*)
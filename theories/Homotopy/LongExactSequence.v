Require Import Basics.
Require Import SuccessorStructure.
Require Import Spaces.Finite.
Require Import Pointed.
Require Import Homotopy.HomotopyGroup.
Require Import Truncations.
Require Import ExactSequence.

Local Open Scope succ_scope.
Local Open Scope pointed_scope.
Import TrIdM.
Set Implicit Arguments.

Notation "'Hexists' x .. y , p" := (hexists (fun x => .. (hexists (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'Hexists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.

Local Notation pt := (point _).

Record LongExactSequence (k : Modality) (N : SuccStr) : Type :=
{ les_carrier : N -> pType;
  les_fn : forall n, les_carrier n.+1 ->* les_carrier n;
  les_iscomplex : forall n, IsComplex (les_fn n.+1) (les_fn n);
  les_isexact : forall n, IsExact k (les_fn n.+1) (les_fn n)}.

Coercion les_carrier : LongExactSequence >-> Funclass.
Global Existing Instance les_iscomplex.
Global Existing Instance les_isexact.

(* Do we still need this? *)
(*
Definition transfer_long_exact_sequence {N : SuccStr} {X : LongExactSequence N}
  {Y : N -> pType}
  (H : forall n, IsHSet (Y n))
  (g : forall {n}, Y n.+1 ->* Y n)
  (e : forall {n}, X n <~>* Y n)
  (p : forall n (x : X n.+1), e (fn X n x) = g (e x)) : LongExactSequence N.
Proof.
  apply (Build_LongExactSequence N Y H g).
  + intro n. equiv_intro (e n.+1.+1) x.
    refine (ap (g _) (p _ x)^ @ _). refine ((p _ _)^ @ _).
    refine (ap (e n) (is_chain_complex X n _) @ _).
    apply point_eq.
  + intros n y q.
    assert (H2 : fn X n ((e _)^-1* y) = pt).
    { revert y q. equiv_intro (e n.+1) x. intro q.
      refine (ap (fn X n) (eissect _ _) @ (eissect (e _) _)^ @ _).
      refine (ap (e n)^-1* (p _ _ @ q) @ point_eq (e n)^-1* ). }
    refine (Trunc_rec _ (is_exact X _ _ H2)).
    destruct 1 as [x r].
    refine (tr (e _ x; _)).
    refine ((p _ x)^ @ ap (e _) r @ eisretr _ _).
Defined.
*)





(** The Long Exact Sequence of Homotopy Groups *)

Local Notation "'0'" := (inl (inl (inr tt))).
Local Notation "'1'" := (inl (inr tt)).
Local Notation "'2'" := (inr tt).

Definition loops_carrier (F X Y : pType) (n : N3) : pType :=
  match n with
  | (n, inl (inl (inl x))) => Empty_ind _ x
  | (n, 0) => iterated_loops n Y
  | (n, 1) => iterated_loops n X
  | (n, 2) => iterated_loops n F
  end.

(* I don't know why [oo] stopped working here; [Tr n] still works. *)
Definition loops_les {F X Y : pType} (i : F ->* X) (f : X ->* Y) `{IsExact (Mod_inr oo) F X Y i f}
  : LongExactSequence (Tr (-1)) (N3).
Proof.
  srefine (Build_LongExactSequence (N3) (loops_carrier F X Y) _ _ _).
  all:intros [n [[[[]|[]]|[]]|[]]]; cbn.
  - apply iterated_loops_functor; exact f.
  - apply iterated_loops_functor; exact i.
  - srapply Build_pMap.
    
    refine (_ o* unfold_iterated_loops' n Y).
    apply iterated_loops_functor.
    exact (pfib (pfib f) o* (pfiber2_loops f)^-1* ).
  - srefine (Build_pHomotopy _ _).
    + intros x; cbn.



Definition homotopy_groups {X Y : pType} (f : X ->* Y) (n : N3) : pType :=
  match n with
  | (n, inl (inl (inl x))) => Empty_ind _ x
  | (n, 0) => Pi n Y
  | (n, 1) => Pi n X
  | (n, 2) => Pi n (pfiber f)
  end.

(** A pointed version pi_loops. *)
(* move *)
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

(* move *)
Global Instance is_hset_pi n X : IsHSet (Pi n X).
Proof.
  destruct n; exact _.
Defined.

(** The long exact sequence of homotopy groups of a pointed map *)
Definition LES_homotopy {X Y : pType} (f : X ->* Y) : LongExactSequence (N3).
Proof.
  srefine (Build_LongExactSequence _ (homotopy_groups f) _ (homotopy_groups_hom f) _ _).
  + intro n. destruct n as [n [[[[]|[]]|[]]|[]]]. 
    all: simpl; exact _.
  + admit.
  + admit.
Admitted.

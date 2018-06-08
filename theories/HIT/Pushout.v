(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics.
Require Import Types.Paths Types.Forall Types.Sigma Types.Arrow Types.Universe Types.Unit Types.Sum.
Require Import HSet TruncType.
Require Export HIT.Coeq.
Require Import HIT.Truncations.
Import TrM.
Local Open Scope path_scope.


(** * Homotopy Pushouts *)

(*
Record Span :=
  { A : Type; B : Type; C : Type;
    f : C -> A;
    g : C -> B }.

Record Cocone (S : Span) (D : Type) :=
  { i : A S -> D;
    j : B S -> D;
    h : forall c, i (f S c) = j (g S c) }.
*)

(** We define pushouts in terms of coproducts and coequalizers. *)

Definition pushout {A B C : Type} (f : A -> B) (g : A -> C) : Type
  := Coeq (inl o f) (inr o g).

Definition push {A B C : Type} {f : A -> B} {g : A -> C}
 : B+C -> pushout f g
  := @coeq _ _ (inl o f) (inr o g).

Definition pushl {A B C} {f : A -> B} {g : A -> C} (b : B) : pushout f g := push (inl b).
Definition pushr {A B C} {f : A -> B} {g : A -> C} (c : C) : pushout f g := push (inr c).

Definition pp {A B C : Type} {f : A -> B} {g : A -> C} (a : A) : pushl (f a) = pushr (g a)
  := @cp A (B+C) (inl o f) (inr o g) a.

Definition pushout_ind {A B C} (f : A -> B) (g : A -> C) (P : pushout f g -> Type)
  (pushb : forall b : B, P (pushl b))
  (pushc : forall c : C, P (pushr c))
  (pp' : forall a : A, (pp a) # (pushb (f a)) = pushc (g a))
  : forall (w : pushout f g), P w
  := Coeq_ind P (fun bc => match bc with inl b => pushb b | inr c => pushc c end) pp'.

Definition pushout_ind_beta_pp {A B C f g}
           (P : @pushout A B C f g -> Type)
           (pushb : forall b : B, P (push (inl b)))
           (pushc : forall c : C, P (push (inr c)))
           (pp' : forall a : A, (pp a) # (pushb (f a)) = pushc (g a)) (a : A)
: apD (pushout_ind f g P pushb pushc pp') (pp a) = pp' a
  := Coeq_ind_beta_cp P (fun bc => match bc with inl b => pushb b | inr c => pushc c end) pp' a.

(** But we want to allow the user to forget that we've defined pushouts in terms of coequalizers. *)
Arguments pushout : simpl never.
Arguments push : simpl never.
Arguments pp : simpl never.
Arguments pushout_ind : simpl never.
Arguments pushout_ind_beta_pp : simpl never.

Definition pushout_rec {A B C} {f : A -> B} {g : A -> C} (P : Type)
  (pushb : B -> P)
  (pushc : C -> P)
  (pp' : forall a : A, pushb (f a) = pushc (g a))
  : @pushout A B C f g -> P
  := pushout_ind f g (fun _ => P) pushb pushc (fun a => transport_const _ _ @ pp' a).

Definition pushout_rec_beta_pp {A B C f g} (P : Type)
  (pushb : B -> P)
  (pushc : C -> P)
  (pp' : forall a : A, pushb (f a) = pushc (g a))
  (a : A)
  : ap (pushout_rec P pushb pushc pp') (pp a) = pp' a.
Proof.
  unfold pushout_rec.
  eapply (cancelL (transport_const (pp a) _)).
  refine ((apD_const (@pushout_ind A B C f g (fun _ => P) pushb pushc _) (pp a))^ @ _).
  refine (pushout_ind_beta_pp (fun _ => P) _ _ _ _).
Defined.

(** ** Symmetry *)

Definition pushout_sym_map {A B C} {f : A -> B} {g : A -> C}
  : pushout f g -> pushout g f
  := pushout_rec (pushout g f) pushr pushl (fun a : A => (pp a)^).

Lemma sect_pushout_sym_map {A B C f g} : Sect (@pushout_sym_map A C B g f) (@pushout_sym_map A B C f g).
Proof.
  unfold Sect. srapply @pushout_ind.
  - intros; reflexivity.
  - intros; reflexivity.
  - intro a.
    abstract (rewrite transport_paths_FFlr, pushout_rec_beta_pp, ap_V, pushout_rec_beta_pp; hott_simpl).
Defined.

Definition pushout_sym {A B C} {f : A -> B} {g : A -> C} : pushout f g <~> pushout g f :=
equiv_adjointify pushout_sym_map pushout_sym_map sect_pushout_sym_map sect_pushout_sym_map.

(** ** Equivalences *)

(** Pushouts preserve equivalences. *)

Lemma equiv_pushout {A B C f g A' B' C' f' g'}
  (eA : A <~> A') (eB : B <~> B') (eC : C <~> C')
  (p : eB o f == f' o eA) (q : eC o g == g' o eA)
  : pushout f g <~> pushout f' g'.
Proof.
  refine (equiv_functor_coeq' eA (equiv_functor_sum' eB eC) _ _).
  all:unfold pointwise_paths.
  all:intro; simpl; apply ap.
  + apply p.
  + apply q.
Defined.

Lemma equiv_pushout_pp {A B C f g A' B' C' f' g'}
  {eA : A <~> A'} {eB : B <~> B'} {eC : C <~> C'}
  {p : eB o f == f' o eA} {q : eC o g == g' o eA}
  : forall a : A, ap (equiv_pushout eA eB eC p q) (pp a)
    = ap push (ap inl (p a)) @ pp (eA a) @ ap push (ap inr (q a))^.
Proof.
  apply @functor_coeq_beta_cp.
Defined.

(** ** Cones of hsets *)

Section SetCone.
  Context {A B : hSet} (f : A -> B).

  Definition setcone := Trunc 0 (pushout f (const tt)).

  Global Instance istrunc_setcone : IsHSet setcone := _.

  Definition setcone_point : setcone := tr (push (inr tt)).
End SetCone.


(* The pushout of an injection between sets is a set *)

Section SPM.
  Context {A B C : Type}
          {aset : IsHSet A} {bset : IsHSet B} {cset : IsHSet C}
          (f : A -> B) (g : A -> C) {fmono : isinj f}
          {ua : Univalence}.

  Definition P := pushout f g.

  Definition code : P -> P -> Type.
  Proof.
    transparent assert (codeb : (B -> P -> Type)).
    { intros b. 
      transparent assert (codebb : (B -> Type)).
      { intros b'.
        pose (X := { a : A & ((b = f a) * (b' = f a)) }).
        pose (Y := { a : A & { a' : A & ((b = f a) * (b' = f a') * (g a = g a')) } }).
        pose (gamma := (fun x:X => (fst x.2) @ (snd x.2)^) : X -> (b = b')).
        pose (lambda := (fun x:X => (x.1 ; (x.1 ; (fst x.2 , snd x.2 , idpath )))) : X -> Y).
        exact (pushout gamma lambda).
      } 
      transparent assert (codebc : (C -> Type)).
      { exact (fun c => { a:A & (b = f a) * (c = g a)}). }
      refine (pushout_rec _ codebb codebc _).
      intros a.
      subst codebb codebc.
      cbn.
      admit.
    }
    transparent assert (codec : (C -> P -> Type)).
    { clear codeb.
      intros c.
      pose (codecb := (fun b => { a:A & (c = g a) * (b = f a)}) : (B -> Type)).
      pose (codecc := (fun c' => (c = c')) : (C -> Type)).
      refine (pushout_rec _ codecb codecc _).
      intros a.
      subst codecb codecc.
      cbn.
      apply path_universe_uncurried.
      transparent assert (h : ({a0 : A & (c = g a0) * (f a = f a0)} -> (c = g a))).
      { intros x.
        destruct x as [a' [p q]].
        exact (p @ (ap g (fmono a a' q))^).
      }
      transparent assert (k : ((c = g a) -> {a0 : A & (c = g a0) * (f a = f a0)})).
      { intros p.
        exact (a ; (p , idpath)).
      }
      refine (equiv_adjointify h k _ _).
      { intros x.
        subst h k. cbn.
        apply path_ishprop.
      }
      { intros y.
        destruct y as [a' [p q]].
        subst h k. cbn.
        admit. }
    }
    refine (pushout_rec _ codeb codec _).
    
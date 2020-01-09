(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.

(** * Wild categories, functors, and transformations *)

(** ** 0-coherent 0-categories *)

(** A 0-coherent 0-category is just a directed graph. *)
Class IsGraph (A : Type) :=
{
  Hom : A -> A -> Type
}.

Notation "a $-> b" := (Hom a b).

(** ** 0-coherent 1-categorical structures *)

(** A 0-coherent 1-category has 1-morphisms and operations on them, but no coherence. *)
Class Is0Coh1Cat (A : Type) := Build_Is0Coh1Cat'
{
  isgraph_1cat : IsGraph A;
  Id  : forall (a : A), a $-> a;
  cat_comp : forall (a b c : A), (b $-> c) -> (a $-> b) -> (a $-> c);
}.

Global Existing Instance isgraph_1cat.
Arguments cat_comp {A _ a b c} _ _.
Notation "g $o f" := (cat_comp g f).

Definition Build_Is0Coh1Cat A
           (Hom' : A -> A -> Type)
           (Id'  : forall (a : A), Hom' a a)
           (cat_comp' : forall (a b c : A), Hom' b c -> Hom' a b -> Hom' a c)
  : Is0Coh1Cat A
  := Build_Is0Coh1Cat' A (Build_IsGraph A Hom') Id' cat_comp'.

(** A 0-coherent 1-groupoid is a 0-coherent 1-category whose morphisms can be reversed. *)
Class Is0Coh1Gpd (A : Type) `{Is0Coh1Cat A} :=
  { gpd_rev : forall {a b : A}, (a $-> b) -> (b $-> a) }.

Definition GpdHom {A} `{Is0Coh1Gpd A} (a b : A) := a $-> b.
Notation "a $== b" := (GpdHom a b).

Global Instance reflexive_GpdHom {A} `{Is0Coh1Gpd A}
  : Reflexive GpdHom
  := fun a => Id a.

Definition gpd_comp {A} `{Is0Coh1Gpd A} {a b c : A}
  : (a $== b) -> (b $== c) -> (a $== c)
  := fun p q => q $o p.
Infix "$@" := gpd_comp.

Global Instance transitive_GpdHom {A} `{Is0Coh1Gpd A}
  : Transitive GpdHom
  := fun a b c f g => f $@ g.

Notation "p ^$" := (gpd_rev p).

Global Instance symmetric_GpdHom {A} `{Is0Coh1Gpd A}
  : Symmetric GpdHom
  := fun a b f => f^$.

Definition GpdHom_path {A} `{Is0Coh1Gpd A} {a b : A} (p : a = b)
  : a $== b.
Proof.
  destruct p; apply Id.
Defined.

(** A 0-coherent 1-functor acts on morphisms, but satisfies no axioms. *)
Class Is0Coh1Functor {A B : Type} `{IsGraph A} `{IsGraph B} (F : A -> B)
  := { fmap : forall (a b : A) (f : a $-> b), F a $-> F b }.

Arguments fmap {_ _ _ _} F {_ _ _} f.

(** Products preserve 0-coherent 1-categories. *)
Global Instance is0coh0cat_prod A B `{IsGraph A} `{IsGraph B}
  : IsGraph (A * B)
  := Build_IsGraph (A * B) (fun x y => (fst x $-> fst y) * (snd x $-> snd y)).

Global Instance is0coh1cat_prod A B `{Is0Coh1Cat A} `{Is0Coh1Cat B}
  : Is0Coh1Cat (A * B).
Proof.
  refine (Build_Is0Coh1Cat (A * B) (fun x y => (fst x $-> fst y) * (snd x $-> snd y)) _ _).
  - intros [a b]; exact (Id a, Id b).
  - intros [a1 b1] [a2 b2] [a3 b3] [f1 g1] [f2 g2]; cbn in *.
    exact (f1 $o f2 , g1 $o g2).
Defined.

(** To avoid having to define a separate notion of "two-variable functor", we define two-variable functors in uncurried form.  The following definition applies such a two-variable functor, with a currying built in. *)
Definition fmap11 {A B C : Type} `{IsGraph A} `{IsGraph B} `{IsGraph C}
  (F : A -> B -> C) {H2 : Is0Coh1Functor (uncurry F)}
  {a1 a2 : A} {b1 b2 : B} (f1 : a1 $-> a2) (f2 : b1 $-> b2)
  : F a1 b1 $-> F a2 b2
  := @fmap _ _ _ _ (uncurry F) H2 (a1, b1) (a2, b2) (f1, f2).


(** ** 0-coherent (2,1)-categorical structures *)

(** A 0-coherent (2,1)-category has its hom-types enhanced to 0-coherent 1-groupoids and its composition operations to 0-coherent 1-functors. *)
Class Is0Coh2Cat (A : Type) `{Is0Coh1Cat A} :=
{
  is0coh1cat_hom : forall (a b : A), Is0Coh1Cat (a $-> b) ;
  isgpd_hom : forall (a b : A), Is0Coh1Gpd (a $-> b) ;
  is0coh1functor_comp : forall (a b c : A), Is0Coh1Functor (uncurry (@cat_comp A _ a b c))
}.
Global Existing Instance is0coh1cat_hom.
Global Existing Instance isgpd_hom.
Global Existing Instance is0coh1functor_comp.

Definition Comp2 {A} `{Is0Coh2Cat A} {a b c : A}
           {f g : a $-> b} {h k : b $-> c}
           (q : h $-> k) (p : f $-> g)
  : (h $o f $-> k $o g)
  := fmap11 cat_comp q p.

Infix "$o@" := Comp2.

Definition WhiskerL_Htpy {A} `{Is0Coh2Cat A} {a b c : A}
           {f g : a $-> b} (h : b $-> c) (p : f $-> g)
  : h $o f $-> h $o g
  := (Id h) $o@ p.
Notation "h $@L p" := (WhiskerL_Htpy h p).

Definition WhiskerR_Htpy {A} `{Is0Coh2Cat A} {a b c : A}
           {f g : b $-> c} (p : f $-> g) (h : a $-> b)
  : f $o h $-> g $o h
  := p $o@ (Id h).
Notation "p $@R h" := (WhiskerR_Htpy p h).

(** Generalizing function extensionality, "Morphism extensionality" states that homwise [GpdHom_path] is an equivalence. *)
Class HasMorExt (A : Type) `{Is0Coh2Cat A} :=
  { isequiv_Htpy_path : forall a b f g, IsEquiv (@GpdHom_path (a $-> b) _ _ f g) }.
Global Existing Instance isequiv_Htpy_path.

Definition path_hom {A} `{HasMorExt A} {a b : A} {f g : a $-> b} (p : f $== g) : f = g
  := GpdHom_path^-1 p.

(** A 0-coherent (2,1)-functor acts on 2-cells, but satisfies no axioms. *)
Class Is0Coh2Functor {A B : Type} `{Is0Coh2Cat A} `{Is0Coh2Cat B}
  (* We can't write `{Is0Coh1Functor A B F} since that would duplicate the instances of Is0Coh1Cat. *)
  (F : A -> B) {ff : Is0Coh1Functor F}
  := { fmap2 : forall a b (f g : a $-> b), (f $== g) -> (fmap F f $== fmap F g) }.

Arguments fmap2 {_ _ _ _ _ _} F {_ _ _ _ _ _} p.

(** ** 1-coherent 1-categorical structures *)

(** A 1-coherent 1-category satisfies associativity and unit laws up to 2-cells (so it must be at least a 0-coherent 2-category).  We duplicate the reversed associativity and double-identity laws to make more duality operations definitionally involutive. *)
Class Is1Coh1Cat (A : Type) `{Is0Coh2Cat A} := Build_Is1Coh1Cat'
{
  cat_assoc : forall a b c d (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f $== h $o (g $o f);
  cat_assoc_opp : forall a b c d (f : a $-> b) (g : b $-> c) (h : c $-> d),
    h $o (g $o f) $== (h $o g) $o f;
  cat_idl : forall a b (f : a $-> b), Id b $o f $== f;
  cat_idr : forall a b (f : a $-> b), f $o Id a $== f;
  cat_idlr : forall a, Id a $o Id a $== Id a;
}.

(* But in practice we don't want to have to give those extra data. *)
Definition Build_Is1Coh1Cat (A : Type) `{Is0Coh2Cat A}
 (cat_assoc' : forall a b c d (f : a $-> b) (g : b $-> c) (h : c $-> d),
  (h $o g) $o f $== h $o (g $o f))
 (cat_idl' : forall a b (f : a $-> b), Id b $o f $== f)
 (cat_idr' : forall a b (f : a $-> b), f $o Id a $== f)
  : Is1Coh1Cat A
  := Build_Is1Coh1Cat' A _ _ cat_assoc'
      (fun a b c d f g h => (cat_assoc' a b c d f g h)^$)
      cat_idl' cat_idr' (fun a => cat_idl' a a (Id a)).

Arguments cat_assoc {_ _ _ _ _ _ _ _} f g h.
Arguments cat_assoc_opp {_ _ _ _ _ _ _ _} f g h.
Arguments cat_idl {_ _ _ _ _ _} f.
Arguments cat_idr {_ _ _ _ _ _} f.
Arguments cat_idlr {_ _ _ _} a.

(** Often, the coherences are actually equalities rather than homotopies. *)
Class Is1Coh1Cat_Strong (A : Type) `{Is0Coh2Cat A} := Build_Is1Coh1Cat_Strong'
{
  cat_assoc_strong : forall a b c d
    (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f = h $o (g $o f);
  cat_assoc_opp_strong : forall a b c d
    (f : a $-> b) (g : b $-> c) (h : c $-> d),
    h $o (g $o f) = (h $o g) $o f;
  cat_idl_strong : forall a b (f : a $-> b), Id b $o f = f;
  cat_idr_strong : forall a b (f : a $-> b), f $o Id a = f;
  cat_idlr_strong : forall a, Id a $o Id a = Id a;
}.

Definition Build_Is1Coh1Cat_Strong (A : Type) `{Is0Coh2Cat A}
  (cat_assoc' : forall a b c d (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f = h $o (g $o f))
  (cat_idl' : forall a b (f : a $-> b), Id b $o f = f)
  (cat_idr' : forall a b (f : a $-> b), f $o Id a = f)
  : Is1Coh1Cat_Strong A
  := Build_Is1Coh1Cat_Strong' A _ _ cat_assoc'
    (fun a b c d f g h => (cat_assoc' a b c d f g h)^)
    cat_idl' cat_idr' (fun a => cat_idl' a a (Id a)).

Arguments cat_assoc_strong {_ _ _ _ _ _ _ _} f g h.
Arguments cat_assoc_opp_strong {_ _ _ _ _ _ _ _} f g h.
Arguments cat_idl_strong {_ _ _ _ _ _} f.
Arguments cat_idr_strong {_ _ _ _ _ _} f.
Arguments cat_idlr_strong {_ _ _ _} a.

Global Instance is1coh1cat_strong A
       {ac0 : Is0Coh1Cat A} {ac2 : Is0Coh2Cat A}
       {ac11 : Is1Coh1Cat_Strong A} : Is1Coh1Cat A.
Proof.
  srapply Build_Is1Coh1Cat'; intros; apply GpdHom_path.
  - serapply cat_assoc_strong.
  - serapply cat_assoc_opp_strong.
  - serapply cat_idl_strong.
  - serapply cat_idr_strong.
  - serapply cat_idlr_strong.
Defined.

(** A 1-coherent 1-functor preserves identities and composition up to a 2-cell, so its codomain at least must be a 0-coherent (2,1)-category. *)
Class Is1Coh1Functor {A B : Type} `{Is0Coh1Cat A} `{Is0Coh2Cat B}
  (F : A -> B) {ff : Is0Coh1Functor F} :=
{
  fmap_id : forall a, fmap F (Id a) $== Id (F a);
  fmap_comp : forall a b c (f : a $-> b) (g : b $-> c),
    fmap F (g $o f) $== fmap F g $o fmap F f;
}.

Arguments fmap_id {_ _ _ _ _} F {_ _} a.
Arguments fmap_comp {_ _ _ _ _} F {_ _ _ _ _} f g.

(** ** Natural transformations *)

Definition Transformation {A B : Type} `{IsGraph B} (F : A -> B) (G : A -> B)
  := forall (a : A), F a $-> G a.

Notation "F $=> G" := (Transformation F G).

(** A 1-coherent natural transformation is natural up to a 2-cell, so again its codomain must be a (2,1)-category. *)
Class Is1Natural {A B : Type} `{IsGraph A} `{Is0Coh2Cat B}
      (F : A -> B) {ff1 : Is0Coh1Functor F} (G : A -> B) {fg1 : Is0Coh1Functor G}
      (alpha : F $=> G) := Build_Is1Natural'
{
  (* Again we duplicate data, to make more opposites definitionally involutive. *)
  isnat : forall a b (f : a $-> b),
    alpha b $o fmap F f $== fmap G f $o alpha a;
  isnat_opp : forall a b (f : a $-> b),
    fmap G f $o alpha a $== alpha b $o fmap F f;
}.

Arguments isnat {_ _ _ _ _ _ _ _ _} alpha {alnat _ _} f : rename.

Definition Build_Is1Natural {A B : Type} `{IsGraph A} `{Is0Coh2Cat B}
           (F : A -> B) {ff1 : Is0Coh1Functor F} (G : A -> B)
           {fg1 : Is0Coh1Functor G} (alpha : F $=> G)
           (isnat' : forall a b (f : a $-> b), alpha b $o fmap F f $== fmap G f $o alpha a)
  : Is1Natural F G alpha
  := Build_Is1Natural' _ _ _ _ _ F _ G _ alpha
                       isnat' (fun a b f => (isnat' a b f)^$).

(** Modifying a transformation to something pointwise equal preserves naturality. *)
Definition is1natural_homotopic {A B : Type} `{Is0Coh1Cat A} `{Is0Coh2Cat B}
      {F : A -> B} {ff1 : Is0Coh1Functor F} {G : A -> B} {fg1 : Is0Coh1Functor G}
      {alpha : F $=> G} (gamma : F $=> G) {gmnat : Is1Natural F G gamma}
      (p : forall a, alpha a $== gamma a)
  : Is1Natural F G alpha.
Proof.
  refine (Build_Is1Natural F G alpha _); intros a b f.
  refine ((p b $@R fmap F f) $@ _).
  refine (_ $@ (fmap G f $@L (p a)^$)).
  apply (isnat gamma).
Defined.

(** Identity functor *)

Section IdentityFunctor.

  Context {A : Type} {H1 : Is0Coh1Cat A}
    {H2 : Is0Coh2Cat A} {H3 : Is1Coh1Cat A}.

  Global Instance is0coh1functor_idmap : Is0Coh1Functor idmap.
  Proof.
    by apply Build_Is0Coh1Functor.
  Defined.

  Global Instance is0coh2functor_idmap : Is0Coh2Functor idmap.
  Proof.
    by apply Build_Is0Coh2Functor.
  Defined.

  Global Instance is1coh1functor_idmap : Is1Coh1Functor idmap.
  Proof.
    by apply Build_Is1Coh1Functor.
  Defined.

End IdentityFunctor.

(** Constant functor *)

Section ConstantFunctor.

  Context {A B : Type}
    {HA1 : Is0Coh1Cat A} {HB1 : Is0Coh1Cat B}
    {HA2 : Is0Coh2Cat A} {HB2 : Is0Coh2Cat B}
    {HA3 : Is1Coh1Cat A} {HB3 : Is1Coh1Cat B}.

  Global Instance is0coh1functor_const (x : B)
    : Is0Coh1Functor (fun _ : A => x).
  Proof.
    serapply Build_Is0Coh1Functor.
    intros a b f; apply Id.
  Defined.

  Global Instance is0coh2functor_const (x : B)
    : Is0Coh2Functor (fun _ : A => x).
  Proof.
    serapply Build_Is0Coh2Functor.
    intros a b f g p; apply Id.
  Defined.

  Global Instance is1coh1functor_const (x : B)
    : Is1Coh1Functor (fun _ : A => x).
  Proof.
    serapply Build_Is1Coh1Functor.
    + intro; apply Id.
    + intros a b c f g. cbn.
      symmetry.
      apply cat_idlr.
  Defined.

End ConstantFunctor.
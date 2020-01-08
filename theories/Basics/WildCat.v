(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.Overture.
Require Import Basics.PathGroupoids.
Require Import Basics.Notations.
Require Import Basics.Contractible.
Require Import Basics.Equivalences.

Local Open Scope path_scope.

(** * Wild categories, functors, and transformations *)

(** ** Unbundled definitions of categories *)

Class Is0Coh1Cat (A : Type) :=
{
  Hom : A -> A -> Type where "a $-> b" := (Hom a b);
  Id  : forall (a : A), a $-> a;
  Comp : forall (a b c : A), (b $-> c) -> (a $-> b) -> (a $-> c);
}.

Notation "a $-> b" := (Hom a b).
Arguments Comp {A _ a b c} _ _.
Notation "g $o f" := (Comp g f).

Class Is0Coh2Cat (A : Type) `{Is0Coh1Cat A} :=
{
  Htpy : forall (a b : A), (a $-> b) -> (a $-> b) -> Type
    where "f $== g" := (Htpy _ _ f g);

  Id_Htpy : forall a b (f : a $-> b), f $== f;

  Opp_Htpy : forall a b (f g : a $-> b), (f $== g) -> (g $== f);

  Concat_Htpy : forall a b (f : a $-> b) (g : a $-> b) (h : a $-> b),
    (f $== g) -> (g $== h) -> (f $== h);

  WhiskerL_Htpy : forall a b c (f g : a $-> b) (h : b $-> c) (p : f $== g),
    (h $o f $== h $o g);

  WhiskerR_Htpy : forall a b c (f g : b $-> c) (p : f $== g) (h : a $-> b),
    (f $o h $== g $o h)
}.

Arguments Htpy {_ _ _ _ _} _ _.
Notation "f $== g" := (Htpy f g).

Arguments Id_Htpy {_ _ _ _ _} f.

Arguments Concat_Htpy {_ _ _ _ _ _ _ _} p q.
Notation "p $@ q" := (Concat_Htpy p q).

Arguments WhiskerL_Htpy {_ _ _ _ _ _ _ _} h p.
Notation "h $@L p" := (WhiskerL_Htpy h p).

Arguments WhiskerR_Htpy {_ _ _ _ _ _ _ _} p h.
Notation "p $@R h" := (WhiskerR_Htpy p h).

Arguments Opp_Htpy {_ _ _ _ _ _ _} p.
Notation "p ^$" := (Opp_Htpy p).

Global Instance Reflexive_Htpy A `{Is0Coh2Cat A} (a b : A)
  : Reflexive (@Htpy A _ _ a b)
  := fun f => Id_Htpy f.

Global Instance Symmetric_Htpy A `{Is0Coh2Cat A} (a b : A)
  : Symmetric (@Htpy A _ _ a b)
  := fun f g p => p^$.

Global Instance Transitive_Htpy A `{Is0Coh2Cat A} (a b : A)
  : Transitive (@Htpy A _ _ a b)
  := fun f g h p q => p $@ q.

Definition as0Coh2CatPath {A : Type} `{Is0Coh1Cat A}
  : Is0Coh2Cat A.
Proof.
  srapply Build_Is0Coh2Cat.
  - intros a b f g; exact (f = g).
  - reflexivity.
  - intros a b f g p ; exact (p ^).
  - intros a b f g h p q ; exact (p @ q).
  - intros a b c f g h p ; apply ap ; exact p.
  - intros a b c f g p h ; exact (ap (fun k => k $o h) p).
Defined.

Definition Htpy_path {A} `{Is0Coh2Cat A} {a b : A} {f g : a $-> b} (p : f = g)
  : f $== g.
Proof.
  destruct p; apply Id_Htpy.
Defined.

(** Generalizing function extensionality, "Morphism extensionality" states that [Htpy_path] is an equivalence. *)
Class HasMorExt (A : Type) `{Is0Coh2Cat A} :=
  { isequiv_Htpy_path : forall a b f g, IsEquiv (@Htpy_path _ _ _ a b f g) }.
Global Existing Instance isequiv_Htpy_path.

Definition path_Htpy {A} `{HasMorExt A} {a b : A} {f g : a $-> b} (p : f $== g) : f = g
  := Htpy_path^-1 p.

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

Global Instance is1coh1cat_strong A
       {ac0 : Is0Coh1Cat A} {ac2 : Is0Coh2Cat A}
       {ac11 : Is1Coh1Cat_Strong A} : Is1Coh1Cat A.
Proof.
  srapply Build_Is1Coh1Cat'; intros; apply Htpy_path.
  - serapply cat_assoc_strong.
  - serapply cat_assoc_opp_strong.
  - serapply cat_idl_strong.
  - serapply cat_idr_strong.
  - serapply cat_idlr_strong.
Defined.

(** ** Unbundled definitions of functors *)

Class Is0Coh1Functor {A B : Type} `{Is0Coh1Cat A} `{Is0Coh1Cat B} (F : A -> B)
  := { fmap : forall (a b : A) (f : a $-> b), F a $-> F b }.

Arguments fmap {_ _ _ _} F {_ _ _} f.

(* We can't write `{Is0Coh1Functor A B F} since that would duplicate the instances of Is0Coh1Cat. *)
Class Is0Coh2Functor {A B : Type} `{Is0Coh2Cat A} `{Is0Coh2Cat B}
  (F : A -> B) {ff : Is0Coh1Functor F}
  := { fmap2 : forall a b (f g : a $-> b), (f $== g) -> (fmap F f $== fmap F g) }.

Arguments fmap2 {_ _ _ _ _ _} F {_ _ _ _ _ _} p.

Class Is1Coh1Functor {A B : Type} `{Is0Coh1Cat A} `{Is0Coh2Cat B}
  (F : A -> B) {ff : Is0Coh1Functor F} :=
{
  fmap_id : forall a, fmap F (Id a) $== Id (F a);
  fmap_comp : forall a b c (f : a $-> b) (g : b $-> c),
    fmap F (g $o f) $== fmap F g $o fmap F f;
}.

Arguments fmap_id {_ _ _ _ _} F {_ _} a.
Arguments fmap_comp {_ _ _ _ _} F {_ _ _ _ _} f g.

(** ** Unbundled definitions of natural transformations *)

Definition Transformation {A B : Type} `{Is0Coh1Cat B} (F : A -> B) (G : A -> B)
  := forall (a : A), F a $-> G a.

Notation "F $--> G" := (Transformation F G).

Class Is1Natural {A B : Type} `{Is0Coh1Cat A} `{Is0Coh2Cat B}
      (F : A -> B) {ff1 : Is0Coh1Functor F} (G : A -> B) {fg1 : Is0Coh1Functor G}
      (alpha : F $--> G) := Build_Is1Natural'
{
  isnat : forall a b (f : a $-> b),
    alpha b $o fmap F f $== fmap G f $o alpha a;
  isnat_opp : forall a b (f : a $-> b),
    fmap G f $o alpha a $== alpha b $o fmap F f;
}.

Arguments isnat {_ _ _ _ _ _ _ _ _} alpha {alnat _ _} f : rename.

Definition Build_Is1Natural {A B : Type} `{Is0Coh1Cat A} `{Is0Coh2Cat B}
           (F : A -> B) {ff1 : Is0Coh1Functor F} (G : A -> B)
           {fg1 : Is0Coh1Functor G} (alpha : F $--> G)
           (isnat' : forall a b (f : a $-> b), alpha b $o fmap F f $== fmap G f $o alpha a)
  : Is1Natural F G alpha
  := Build_Is1Natural' _ _ _ _ _ F _ G _ alpha
                       isnat' (fun a b f => (isnat' a b f)^$).


(** ** Opposite categories *)

Definition op (A : Type) : Type := A.
Notation "A ^op" := (op A).

(** This stops typeclass search from trying to unfold op. *)
Typeclasses Opaque op.

Global Instance is0coh1cat_op A `{Is0Coh1Cat A} : Is0Coh1Cat (A ^op)
  := Build_Is0Coh1Cat A (fun a b => b $-> a) Id (fun a b c g f => f $o g).

Global Instance is0cat2cat_op A `{Is0Coh2Cat A} : Is0Coh2Cat A^op.
Proof.
  srapply Build_Is0Coh2Cat; unfold op in *; cbn in *.
  1: intros a b f g; exact (f $== g).
  all: cbn.
  - intros a b; apply Id_Htpy.
  - intros a b f g; apply Opp_Htpy.
  - intros a b f g h; apply Concat_Htpy.
  - intros a b c f g h p; exact (p $@R h).
  - intros a b c f g p h; exact (h $@L p).
Defined.

Global Instance is1coh1cat_op A `{Is1Coh1Cat A} : Is1Coh1Cat A^op.
Proof.
  srapply Build_Is1Coh1Cat'; unfold op in *; cbn in *.
  - intros a b c d f g h; exact (cat_assoc_opp h g f).
  - intros a b c d f g h; exact (cat_assoc h g f).
  - intros a b f; exact (cat_idr f).
  - intros a b f; exact (cat_idl f).
  - intros a; exact (cat_idlr a).
Defined.

Global Instance is1coh1cat_strong_op A `{Is1Coh1Cat_Strong A}
  : Is1Coh1Cat_Strong (A ^op).
Proof.
  srapply Build_Is1Coh1Cat_Strong'; unfold op in *; cbn in *.
  - intros a b c d f g h; exact (cat_assoc_opp_strong h g f).
  - intros a b c d f g h; exact (cat_assoc_strong h g f).
  - intros a b f; exact (cat_idr_strong f).
  - intros a b f; exact (cat_idl_strong f).
  - intros a; exact (cat_idlr_strong a).
Defined.

(* Opposites are definitionally involutive. You can test this by uncommenting the stuff below. *)
(*
Definition test1 A {ac : Is0Coh1Cat A} : A = (A^op)^op := 1.
Definition test2 A {ac : Is0Coh1Cat A} : ac = is0coh1cat_op (A^op) := 1.
Definition test3 A {ac : Is0Coh1Cat A} {ac2 : Is0Coh2Cat A} : ac2 = is0coh2cat_op (A^op) := 1.
Definition test4 A {ac : Is0Coh1Cat A} {ac2 : Is0Coh2Cat A} {ac11 : Is1Coh1Cat A} : ac11 = is1coh1cat_op (A^op) := 1.
*)

(* Opposite functors and natural transformations *)

Global Instance is0coh1fun_op  A `{Is0Coh1Cat A} B `{Is0Coh1Cat B} (F : A -> B) {ff : Is0Coh1Functor F} : Is0Coh1Functor (F : A ^op -> B ^op).
Proof.
  apply Build_Is0Coh1Functor.
  unfold op.
  cbn.
  intros a b.
  apply fmap.
  exact ff.
Defined.

Global Instance is0coh2fun_op A B `{Is0Coh2Cat A} `{Is0Coh2Cat B}
       (F : A -> B) {ff : Is0Coh1Functor F} {pf : Is0Coh2Functor F} : Is0Coh2Functor (F : A^op -> B^op).
Proof.
  apply Build_Is0Coh2Functor.
  unfold op in *.
  cbn in *.
  intros a b.
  apply fmap2.
  exact pf.
Defined.

Global Instance is1coh1fun_op A B `{Is0Coh1Cat A} `{Is0Coh1Cat B} `{Is0Coh2Cat B} (F : A -> B) {ff : Is0Coh1Functor F} {pf : Is1Coh1Functor F} : Is1Coh1Functor (F : A^op -> B^op).
Proof.
  apply Build_Is1Coh1Functor; unfold op in *; cbn in *.
  - apply fmap_id.
    exact pf.
  - intros a b c.
    intros f g.
    apply fmap_comp.
    exact pf.
Defined.

Print Transformation.

Definition transformation_op {A} {B} `{Is0Coh1Cat B} (F : A -> B) (G : A -> B) (alpha : F $--> G) : (@Transformation (A^op) (B^op) (is0coh1cat_op B) (G : (A^op) -> (B^op)) (F : (A^op) -> (B^op))).
Proof.       
  unfold op in *.
  cbn in *.
  intro a.
  apply (alpha a).
Defined.

Print Is1Natural.

Global Instance is1nat_op A B `{Is0Coh1Cat A} `{Is0Coh2Cat B}
       (F : A -> B) {ff1 : Is0Coh1Functor F} (G : A -> B) {fg1 : Is0Coh1Functor G} (alpha : F $--> G) {pf : Is1Natural F G alpha} : Is1Natural (G : A^op -> B^op) (F : A^op -> B^op) (transformation_op F G alpha).
Proof.
  apply Build_Is1Natural'.
  - unfold op in *.
    unfold transformation_op.
    cbn.
    intros a b f.
    apply isnat_opp.
  - unfold op.
    unfold transformation_op.
    cbn.
    intros a b f.
    apply isnat.
    exact pf.
Defined.

(* Shorter proof of above using Build_Is1Natural. But maybe the longer proof using Build_Is1Natural' is better?

Proof.
  apply Build_Is1Natural.
  unfold op in *.
  cbn in *.
  intros a b.
  unfold transformation_op in *.
  intros f.
  apply isnat_opp.
Defined.
*)
  
(** ** Equivalences *)

(** We could define equivalences in any wild 2-category as bi-invertible maps, or in a wild 3-category as half-adjoint equivalences.  However, in concrete cases there is often an equivalent definition of equivalences that we want to use instead, and the important property we need is that it's logically equivalent to (quasi-)isomorphism. *)

Class HasEquivs (A : Type) `{Is0Coh2Cat A} :=
{
  CatEquiv' : A -> A -> Type where "a $<~> b" := (CatEquiv' a b);
  CatIsEquiv' : forall a b, (a $-> b) -> Type;
  cate_fun' : forall a b, (a $<~> b) -> (a $-> b);
  cate_isequiv' : forall a b (f : a $<~> b), CatIsEquiv' a b (cate_fun' a b f);
  cate_buildequiv' : forall a b (f : a $-> b), CatIsEquiv' a b f -> CatEquiv' a b;
  cate_buildequiv_fun' : forall a b (f : a $-> b) (fe : CatIsEquiv' a b f),
      cate_fun' a b (cate_buildequiv' a b f fe) $== f;
  cate_inv' : forall a b (f : a $-> b), CatIsEquiv' a b f -> (b $-> a);
  cate_issect' : forall a b (f : a $-> b) (fe : CatIsEquiv' a b f),
    cate_inv' _ _ f fe $o f $== Id a;
  cate_isretr' : forall a b (f : a $-> b) (fe : CatIsEquiv' a b f),
      f $o cate_inv' _ _ f fe $== Id b;
  catie_adjointify' : forall a b (f : a $-> b) (g : b $-> a)
    (r : f $o g $== Id b) (s : g $o f $== Id a), CatIsEquiv' a b f;
}.

(** Since apparently a field of a record can't be the source of a coercion (Coq complains about the uniform inheritance condition, although as officially stated that condition appears to be satisfied), we redefine all the fields of [HasEquivs]. *)

Definition CatEquiv {A} `{HasEquivs A} (a b : A)
  := @CatEquiv' A _ _ _ a b.

Notation "a $<~> b" := (CatEquiv a b).
Arguments CatEquiv : simpl never.

Definition cate_fun {A} `{HasEquivs A} {a b : A} (f : a $<~> b)
  : a $-> b
  := @cate_fun' A _ _ _ a b f.

Coercion cate_fun : CatEquiv >-> Hom.

(* Being an equivalence should be a typeclass, but we have to redefine it.  (Apparently [Existing Class] doesn't work.) *)
Class CatIsEquiv {A} `{HasEquivs A} {a b : A} (f : a $-> b)
  := catisequiv : CatIsEquiv' a b f.

Global Instance cate_isequiv {A} `{HasEquivs A} {a b : A} (f : a $<~> b)
  : CatIsEquiv f
  := cate_isequiv' a b f.

Definition Build_CatEquiv {A} `{HasEquivs A} {a b : A}
           (f : a $-> b) {fe : CatIsEquiv f}
  : a $<~> b
  := cate_buildequiv' a b f fe.

Definition cate_buildequiv_fun {A} `{HasEquivs A} {a b : A}
           (f : a $-> b) {fe : CatIsEquiv f}
  : cate_fun (Build_CatEquiv f) $== f
  := cate_buildequiv_fun' a b f fe.

Definition catie_adjointify {A} `{HasEquivs A} {a b : A}
           (f : a $-> b) (g : b $-> a)
           (r : f $o g $== Id b) (s : g $o f $== Id a)
  : CatIsEquiv f
  := catie_adjointify' a b f g r s.

Definition cate_adjointify {A} `{HasEquivs A} {a b : A}
           (f : a $-> b) (g : b $-> a)
           (r : f $o g $== Id b) (s : g $o f $== Id a)
  : a $<~> b
  := @Build_CatEquiv _ _ _ _ a b f (catie_adjointify f g r s).

(** This one we define to construct the whole inverse equivalence. *)
Definition cate_inv {A} `{HasEquivs A} {a b : A} (f : a $-> b) {fe : CatIsEquiv f}
  : b $<~> a.
Proof.
  simple refine (cate_adjointify _ _ _ _).
  - exact (@cate_inv' A _ _ _ a b f fe).
  - exact f.
  - exact (@cate_issect' A _ _ _ a b f fe).
  - exact (@cate_isretr' A _ _ _ a b f fe).
Defined.

Notation "f ^-1$" := (cate_inv f).

Definition cate_issect {A} `{HasEquivs A} {a b} (f : a $-> b) {fe : CatIsEquiv f}
  : f^-1$ $o f $== Id a.
Proof.
  refine (_ $@ @cate_issect' A _ _ _ a b f fe).
  refine (_ $@R f).
  apply cate_buildequiv_fun'.
Defined.

Definition cate_isretr {A} `{HasEquivs A} {a b} (f : a $-> b) {fe : CatIsEquiv f}
  : f $o f^-1$ $== Id b.
Proof.
  refine (_ $@ @cate_isretr' A _ _ _ a b f fe).
  refine (f $@L _).
  apply cate_buildequiv_fun'.
Defined.

(** The identity morphism is an equivalence *)
Global Instance catie_id {A} `{HasEquivs A} {c1 : Is1Coh1Cat A} (a : A)
  : CatIsEquiv (Id a)
  := catie_adjointify (Id a) (Id a) (cat_idlr a) (cat_idlr a).

Definition id_cate {A} `{HasEquivs A} {c1 : Is1Coh1Cat A} (a : A)
  : a $<~> a
  := Build_CatEquiv (Id a).

Global Instance reflexive_cate {A} `{HasEquivs A} {c1 : Is1Coh1Cat A}
  : Reflexive (@CatEquiv A _ _ _)
  := id_cate.

Global Instance symmetric_cate {A} `{HasEquivs A} {c1 : Is1Coh1Cat A}
  : Symmetric (@CatEquiv A _ _ _)
  := fun a b f => cate_inv f.

(** Equivalences can be composed. *)
Definition compose_cate {A} `{HasEquivs A} {c1 : Is1Coh1Cat A} {a b c : A}
  (g : b $<~> c) (f : a $<~> b) : a $<~> c.
Proof.
  refine (cate_adjointify (g $o f) (f^-1$ $o g^-1$) _ _).
  - refine (cat_assoc _ _ _ $@ _).
    refine ((_ $@L cat_assoc_opp _ _ _) $@ _).
    refine ((_ $@L (cate_isretr _ $@R _)) $@ _).
    refine ((_ $@L cat_idl _) $@ _).
    apply cate_isretr.
  - refine (cat_assoc _ _ _ $@ _).
    refine ((_ $@L cat_assoc_opp _ _ _) $@ _).
    refine ((_ $@L (cate_issect _ $@R _)) $@ _).
    refine ((_ $@L cat_idl _) $@ _).
    apply cate_issect.
Defined.

Notation "g $oE f" := (compose_cate g f).

Global Instance transitive_cate {A} `{HasEquivs A} {c1 : Is1Coh1Cat A}
  : Transitive (@CatEquiv A _ _ _)
  := fun a b c f g => g $oE f.


(** Any sufficiently coherent functor preserves equivalences.  *)
Global Instance iemap {A B : Type} `{HasEquivs A} `{HasEquivs B} (F : A -> B)
           {ff1 : Is0Coh1Functor F} {ff2 : Is0Coh2Functor F}
           {ff11 : Is1Coh1Functor F} {a b : A} (f : a $-> b)
           {fe : CatIsEquiv f}
  : CatIsEquiv (fmap F f).
Proof.
  refine (catie_adjointify (fmap F f) (fmap F f^-1$) _ _).
  - refine ((fmap_comp F f^-1$ f)^$ $@ fmap2 F (cate_isretr _) $@ fmap_id F _).
  - refine ((fmap_comp F f f^-1$)^$ $@ fmap2 F (cate_issect _) $@ fmap_id F _).
Defined.

Definition emap {A B : Type} `{HasEquivs A} `{HasEquivs B} (F : A -> B)
           {ff1 : Is0Coh1Functor F} {ff2 : Is0Coh2Functor F}
           {ff11 : Is1Coh1Functor F} {a b : A} (f : a $<~> b)
  : F a $<~> F b
  := Build_CatEquiv (fmap F f).

(** Opposite categories preserve having equivalences. *)
Global Instance hasequivs_op {A} `{HasEquivs A} : HasEquivs A^op.
Proof.
(* TODO: update *)
(*
  srapply Build_HasEquivs; intros a b; unfold op in *; cbn in *.
  1:exact (b $<~> a).
  all:intros f.
  - exact f.
  - exact (f^-1$).
  - cbn. exact (cate_isretr f).
  - cbn. exact (cate_issect f).
  - intros g r s. exact (cate_adjointify f g s r).
  - intros g r s; cbn. apply cate_adjointify_fun.
*)
Admitted.

(** When we have equivalences, we can define what it means for a category to be univalent. *)
Definition cat_equiv_path {A : Type} `{HasEquivs A} {c1 : Is1Coh1Cat A} (a b : A)
  : (a = b) -> (a $<~> b).
Proof.
  intros []; reflexivity.
Defined.

Class IsUnivalent1Cat (A : Type) `{HasEquivs A} {c1 : Is1Coh1Cat A}
  := { isequiv_cat_equiv_path : forall a b, IsEquiv (@cat_equiv_path A _ _ _ _ a b) }.
Global Existing Instance isequiv_cat_equiv_path.

Definition cat_path_equiv {A : Type} `{IsUnivalent1Cat A} (a b : A)
  : (a $<~> b) -> (a = b)
  := (cat_equiv_path a b)^-1.


(** ** The category of types *)

Global Instance is0coh1cat_type : Is0Coh1Cat Type
  := Build_Is0Coh1Cat Type (fun a b => a -> b) (fun a => idmap) (fun a b c g f => g o f).

Global Instance is0coh2cat_type : Is0Coh2Cat Type.
Proof.
  srefine (Build_Is0Coh2Cat Type _ (fun a b f g => f == g) _ _ _ _ _); cbn.
  - intros a b f x; reflexivity.
  - intros a b f g p x; exact ((p x)^).
  - intros a b f g h p q x; exact (p x @ q x).
  - intros a b c f g h p x; exact (ap h (p x)).
  - intros a b c f g p h x; exact (p (h x)).
Defined.

Global Instance is1coh1cat_strong_type : Is1Coh1Cat_Strong Type.
Proof.
  srapply Build_Is1Coh1Cat_Strong'; cbn; intros; reflexivity.
Defined.

Global Instance hasmorext_type `{Funext} : HasMorExt Type.
Proof.
  srapply Build_HasMorExt.
  intros A B f g; cbn in *.
  refine (isequiv_homotopic (@apD10 A (fun _ => B) f g) _).
  intros p.
  destruct p; reflexivity.
Defined.

Global Instance hasequivs_type : HasEquivs Type.
Proof.
  srefine (Build_HasEquivs Type _ _ Equiv (@IsEquiv) _ _ _ _ _ _ _ _); intros A B.
  all:intros f.
  - exact f.
  - exact _.
  - apply Build_Equiv.
  - intros; reflexivity.
  - intros; exact (f^-1).
  - cbn. intros ? x; apply eissect.
  - cbn. intros ? x; apply eisretr.
  - intros g r s; refine (isequiv_adjointify f g r s).
Defined.

(* Of course, this requires the univalence axiom, but (unlike funext, for some reason) that isn't defined until Types/Universe. *)
(*
Global Instance isunivalent_type `{Univalence}
  : IsUnivalent1Cat Type.
*)

(** ** Product categories *)

Global Instance is0coh1cat_prod A B `{Is0Coh1Cat A} `{Is0Coh1Cat B}
  : Is0Coh1Cat (A * B).
Proof.
  refine (Build_Is0Coh1Cat (A * B) (fun x y => (fst x $-> fst y) * (snd x $-> snd y)) _ _).
  - intros [a b]; exact (Id a, Id b).
  - intros [a1 b1] [a2 b2] [a3 b3] [f1 g1] [f2 g2]; cbn in *.
    exact (f1 $o f2 , g1 $o g2).
Defined.

Global Instance is0coh2cat_prod A B `{Is0Coh2Cat A} `{Is0Coh2Cat B}
  : Is0Coh2Cat (A * B).
Proof.
  srefine (Build_Is0Coh2Cat (A * B) _ _ _ _ _ _ _).
  - intros x y f g.
    exact ((fst f $== fst g) * (snd f $== snd g)).
  - intros [a1 b1] [a2 b2] [f g]; split; reflexivity.
  - intros [a1 b1] [a2 b2] [f1 g1] [f2 g2] [p q]; cbn in *.
    exact (p^$, q^$).
  - intros [a1 b1] [a2 b2] [f1 g1] [f2 g2] [f3 g3] [p1 q1] [p2 q2]; cbn in *.
    exact (p1 $@ p2, q1 $@ q2).
  - intros [a1 b1] [a2 b2] [a3 b3] [f1 g1] [f2 g2] [f3 g3] [p q]; cbn in *.
    exact (f3 $@L p , g3 $@L q).
  - intros [a1 b1] [a2 b2] [a3 b3] [f1 g1] [f2 g2] [p q] [f3 g3]; cbn in *.
    exact (p $@R f3, q $@R g3).
Defined.

Global Instance is1coh1cat_prod A B `{Is1Coh1Cat A} `{Is1Coh1Cat B}
  : Is1Coh1Cat (A * B).
Proof.
  srefine (Build_Is1Coh1Cat (A * B) _ _ _ ).
  - intros [a1 a2] [b1 b2] [c1 c2] [d1 d2] [f1 f2] [g1 g2] [h1 h2].
    cbn in *.
    exact(cat_assoc f1 g1 h1, cat_assoc f2 g2 h2).
  - intros [a1 a2] [b1 b2] [f1 f2].
    cbn in *.
    exact (cat_idl _, cat_idl _).
  - intros [a1 a2] [b1 b2] [g1 g2].
    cbn in *.
    exact (cat_idr _, cat_idr _).
Defined.

Global Instance hasequivs_prod A B `{HasEquivs A} `{HasEquivs B}
  : HasEquivs (A * B).
Proof.
  srefine (Build_HasEquivs (A * B) _ _
             (fun a b => (fst a $<~> fst b) * (snd a $<~> snd b))
             _
             _ _ _ _ _ _ _ _).
  1:intros a b f; exact (CatIsEquiv (fst f) * CatIsEquiv (snd f)).
  all:cbn; intros a b f.
  - split; [ exact (fst f) | exact (snd f) ].
  - split; exact _.
  - intros [fe1 fe2]; split.
    + exact (Build_CatEquiv (fst f)).
    + exact (Build_CatEquiv (snd f)).
  - intros [fe1 fe2]; cbn; split; apply cate_buildequiv_fun.
  - intros [fe1 fe2]; split; [ exact ((fst f)^-1$) | exact ((snd f)^-1$) ].
  - intros [fe1 fe2]; split; apply cate_issect.
  - intros [fe1 fe2]; split; apply cate_isretr.
  - intros g r s; split.
    + exact (catie_adjointify (fst f) (fst g) (fst r) (fst s)).
    + exact (catie_adjointify (snd f) (snd g) (snd r) (snd s)).
Defined.

(** ** Sum categories *)

Global Instance is0coh1cat_sum A B `{ Is0Coh1Cat A } `{ Is0Coh1Cat B} 
  : Is0Coh1Cat (A + B).
  srefine (Build_Is0Coh1Cat _ _ _ _).
  - intros [a | b] [a1 | b1].
    + exact (a $-> a1).
    + exact Empty.
    + exact Empty.
    + exact (b $-> b1).
  - cbn.
    intros [a | b].
    + exact (Id a).
    + exact (Id b).
  - intros [a | b] [a1 | b1] [a2 | b2]; try contradiction.
    + intros f g.
    exact (f $o g).
    + intros f g.
    exact (f $o g).
Defined.

(* Note: [try contradiction] deals with empty cases. *)
Global Instance is0coh2cat_sum A B `{ Is0Coh2Cat A } `{ Is0Coh2Cat B} 
  : Is0Coh2Cat (A + B).
Proof.
  srefine (Build_Is0Coh2Cat _ _ _ _ _ _ _ _).
  -intros [a | b] [c | d]; try contradiction.
    + cbn. intros f g. 
    exact ( f $== g ).
    + cbn. intros f g.
    exact (f $== g).
  -intros [a | b] [a1 | b1] ; try contradiction.
    + cbn. intro f. exact (Id_Htpy f).
    + cbn. intro f.  exact (Id_Htpy f).
  -intros [a | b] [a1 | b1] ; try contradiction.
    +cbn. intros f g. 
    exact Opp_Htpy.
    +cbn. intros f g.
    exact Opp_Htpy.
  - intros [a | b] [c | d] f g h; try contradiction.
    + cbn. 
    exact Concat_Htpy.
    + cbn.
    exact Concat_Htpy.
  - intros [a | b] [c | d] [e | f]; try contradiction.
    + cbn. intros f g h. 
    apply WhiskerL_Htpy.
    + cbn. intros t g h.
    apply WhiskerL_Htpy.
  - intros [a | b] [c | d] [e | f]; try contradiction.
    + cbn. intros f g. 
    apply WhiskerR_Htpy.
    + cbn. intros t g.
    apply WhiskerR_Htpy.
    Defined.
    
Global Instance is1coh1cat_sum A B `{Is1Coh1Cat A} `{Is1Coh1Cat B}
  : Is1Coh1Cat (A + B).
Proof.
  srefine (Build_Is1Coh1Cat (A + B) _ _ _ ).
  - intros [a1 | a2] [b1 | b2] [c1 | c2] [d1 | d2] f g h; try contradiction; try contradiction.
    + cbn in *.
    apply cat_assoc.
    + cbn in *.
    apply cat_assoc.
  - intros [a | b] [c | d] f; try contradiction.
    + cbn in *. apply cat_idl.
    + cbn in *. apply cat_idl.
  - intros [a | b] [c | d] f; try contradiction.
    + cbn in *. apply cat_idr.
    + cbn in *. apply cat_idr.
  Defined.
    
    

(** ** Two-variable functors *)

(** To avoid having to define a separate notion of "two-variable functor", we define two-variable functors in uncurried form.  The following definition applies such a two-variable functor, with a currying built in. *)
Definition fmap11 {A B C : Type} `{Is0Coh1Cat A} `{Is0Coh1Cat B} `{Is0Coh1Cat C}
  (F : A -> B -> C) {H2 : Is0Coh1Functor (uncurry F)}
  {a1 a2 : A} {b1 b2 : B} (f1 : a1 $-> a2) (f2 : b1 $-> b2)
  : F a1 b1 $-> F a2 b2
  := @fmap _ _ _ _ (uncurry F) H2 (a1, b1) (a2, b2) (f1, f2).

(** For instance, we have hom-functors. *)
Global Instance is0coh1functor_hom {A} `{Is0Coh1Cat A}
  : @Is0Coh1Functor (A^op * A) Type _ _ (uncurry (@Hom A _)).
Proof.
  apply Build_Is0Coh1Functor.
  intros [a1 a2] [b1 b2] [f1 f2] g; cbn in *.
  exact (f2 $o g $o f1).
Defined.

Global Instance is0coh2functor_hom {A} `{Is0Coh2Cat A}
  : @Is0Coh2Functor (A^op * A) Type _ _ _ _ (uncurry (@Hom A _)) _.
Proof.
  apply Build_Is0Coh2Functor.
  intros [a1 a2] [b1 b2] [f1 f2] [g1 g2] [p1 p2] q; cbn in *.
  (* This needs funext in [A]. *)
Abort.


(** ** Sum categories *)

(* TODO? *)


(** ** Wild functor categories *)

Definition Fun1 (A B : Type) `{Is0Coh1Cat A} `{Is0Coh1Cat B}
  := { F : A -> B & Is0Coh1Functor F }.

Definition NatTrans {A B : Type} `{Is0Coh1Cat A} `{Is0Coh2Cat B} (F G : A -> B)
           {ff : Is0Coh1Functor F} {fg : Is0Coh1Functor G}
  := { alpha : F $--> G & Is1Natural F G alpha }.

(** Note that even if [A] and [B] are fully coherent oo-categories, the objects of our "functor category" are not fully coherent.  Thus we cannot in general expect this "functor category" to itself be fully coherent.  However, it is at least a 0-coherent 1-category, as long as [B] is a 1-coherent 1-category. *)

Global Instance is0coh1cat_fun (A B : Type) `{Is0Coh1Cat A} `{Is1Coh1Cat B} : Is0Coh1Cat (Fun1 A B).
Proof.
  srapply Build_Is0Coh1Cat.
  - intros [F ?] [G ?].
    exact (NatTrans F G).
  - intros [F ?]; cbn.
    exists (fun a => Id (F a)); apply Build_Is1Natural; intros a b f; cbn.
    refine (cat_idl (fmap F f) $@ (cat_idr (fmap F f))^$).
  - intros [F ?] [G ?] [K ?] [gamma ?] [alpha ?]; cbn in *.
    exists (fun a => gamma a $o alpha a).
    apply Build_Is1Natural; intros a b f; cbn.
    refine (cat_assoc _ _ _ $@ _).
    refine ((gamma b $@L isnat alpha f) $@ _).
    refine (cat_assoc_opp _ _ _ $@ _).
    refine ((isnat gamma f) $@R alpha a $@ _).
    exact (cat_assoc _ _ _).
Defined.

(** In fact, in this case it is automatically also a 0-coherent 2-category and a 1-coherent 1-category, with a totally incoherent notion of 2-cell between 1-coherent natural transformations. *)

Global Instance is0coh2cat_fun (A B : Type) `{Is0Coh1Cat A} `{Is1Coh1Cat B} : Is0Coh2Cat (Fun1 A B).
Proof.
  srapply Build_Is0Coh2Cat.
  - intros [F ?] [G ?] [alpha ?] [gamma ?].
    exact (forall a, alpha a $== gamma a).
  - intros [F ?] [G ?] [alpha ?] a; cbn.
    reflexivity.
  - intros [F ?] [G ?] [alpha ?] [gamma ?] mu a.
    exact ((mu a)^$).
  - intros [F ?] [G ?] [alpha ?] [gamma ?] [phi ?] mu nu a.
    exact (mu a $@ nu a).
  - intros [F ?] [G ?] [K ?] [alpha ?] [gamma ?] [phi ?] mu a; cbn.
    exact (phi a $@L mu a).
  - intros [F ?] [G ?] [K ?] [alpha ?] [gamma ?] mu [phi ?] a; cbn.
    exact (mu a $@R phi a).
Defined.

Global Instance is1coh1cat_fun (A B : Type) `{Is0Coh1Cat A} `{Is1Coh1Cat B} : Is1Coh1Cat (Fun1 A B).
Proof.
  srapply Build_Is1Coh1Cat'.
  1,2:intros [F ?] [G ?] [K ?] [L ?] [alpha ?] [gamma ?] [phi ?] a; cbn.
  3,4:intros [F ?] [G ?] [alpha ?] a; cbn.
  5:intros [F ?] a; cbn.
  - serapply cat_assoc.
  - serapply cat_assoc_opp.
  - serapply cat_idl.
  - serapply cat_idr.
  - serapply cat_idlr.
Defined.

(** It also inherits a notion of equivalence, namely a natural transformation that is a pointwise equivalence.  Note that due to incoherence, in this case we do *not* expect [cat_unadjointify] and [cat_adjointify] to actually be inverses. *)

(* TODO: update *)

(*
Definition NatEquiv {A B : Type} `{Is0Coh1Cat A} `{HasEquivs B} (F G : A -> B) {ff : Is0Coh1Functor F} {fg : Is0Coh1Functor G}
  := { alpha : forall a, F a $<~> G a & Is1Natural F G (fun a => alpha a) }.

Global Instance hasequivs_fun (A B : Type) `{Is1Coh1Cat A} `{Is1Coh1Cat B}
  {eB : HasEquivs B} : HasEquivs (Fun1 A B).
Proof.
  srapply Build_HasEquivs.
  - intros [F ?] [G ?]. exact (NatEquiv F G).
  - intros [F ?] [G ?] [alpha alnat]. cbn.
    exists (fun a => alpha a); assumption.
  - intros [F ?] [G ?] [alpha alnat]. cbn.
    exists (fun a => (alpha a)^-1$).
    apply Build_Is1Natural; intros a b f.
    refine ((cat_idr _)^$ $@ _).
    refine ((_ $@L (cate_isretr (alpha a))^$) $@ _).
    refine (cat_assoc _ _ _ $@ _).
    refine ((_ $@L (cat_assoc_opp _ _ _)) $@ _).
    refine ((_ $@L ((isnat (fun a => alpha a) f)^$ $@R _)) $@ _).
    refine ((_ $@L (cat_assoc _ _ _)) $@ _).
    refine (cat_assoc_opp _ _ _ $@ _).
    refine ((cate_issect (alpha b) $@R _) $@ _).
    exact (cat_idl _).
  - intros [F ?] [G ?] [alpha alnat] a; apply cate_issect.
  - intros [F ?] [G ?] [alpha alnat] a; apply cate_isretr.
  - intros [F ?] [G ?] [alpha ?] [gamma ?] r s; cbn in *.
    exists (fun a => cate_adjointify (alpha a) (gamma a) (r a) (s a)).
    apply Build_Is1Natural; intros a b f.
    refine ((cate_adjointify_fun _ _ _ _ $@R _) $@ _); cbn.
    refine (_ $@ (_ $@L cate_adjointify_fun _ _ _ _)^$); cbn.
    exact (isnat alpha f).
  - intros [F ?] [G ?] [alpha ?] [gamma ?] r s a; cbn in *.
    apply cate_adjointify_fun.
Defined.
*)


(** ** The covariant Yoneda lemma *)

(** This is easier than the contravariant version because it doesn't involve any "op"s. *)

Definition opyon {A : Type} `{Is0Coh1Cat A} (a : A) : A -> Type
  := fun b => (a $-> b).

Global Instance is0coh1functor_opyon {A : Type} `{Is0Coh1Cat A} (a : A)
  : Is0Coh1Functor (opyon a).
Proof.
  apply Build_Is0Coh1Functor.
  unfold opyon; intros b c f g; cbn in *.
  exact (f $o g).
Defined.

Definition opyoneda {A : Type} `{Is0Coh1Cat A} (a : A)
           (F : A -> Type) {ff : Is0Coh1Functor F}
  : F a -> (opyon a $--> F).
Proof.
  intros x b f.
  exact (fmap F f x).
Defined.

Definition un_opyoneda {A : Type} `{Is0Coh1Cat A}
  (a : A) (F : A -> Type) {ff : Is0Coh1Functor F}
  : (opyon a $--> F) -> F a
  := fun alpha => alpha a (Id a).

Global Instance is1natural_opyoneda {A : Type} `{Is0Coh2Cat A}
  (a : A) (F : A -> Type) {ff : Is0Coh1Functor F} {ff1 : Is1Coh1Functor F} (x : F a)
  : Is1Natural (opyon a) F (opyoneda a F x).
Proof.
  apply Build_Is1Natural.
  unfold op, opyon, opyoneda; intros b c f g; cbn in *.
  exact (fmap_comp F g f x).
Defined.

Definition opyoneda_issect {A : Type} `{Is0Coh2Cat A} (a : A)
           (F : A -> Type) {ff : Is0Coh1Functor F} {ff1 : Is1Coh1Functor F}
           (x : F a)
  : un_opyoneda a F (opyoneda a F x) = x
  := fmap_id F a x.

(** We assume for the converse that the coherences in [A] are equalities (this is a weak funext-type assumption).  Note that we do not in general recover the witness of 1-naturality.  Indeed, if [A] is fully coherent, then a transformation of the form [yoneda a F x] is always also fully coherently natural, so an incoherent witness of 1-naturality could not be recovered in this way.  *)
Definition opyoneda_isretr {A : Type} `{Is1Coh1Cat_Strong A} (a : A)
           (F : A -> Type) {ff : Is0Coh1Functor F} {ff1 : Is1Coh1Functor F}
           (alpha : opyon a $--> F) {alnat : Is1Natural (opyon a) F alpha}
           (b : A)
  : opyoneda a F (un_opyoneda a F alpha) b $== alpha b.
Proof.
  unfold opyoneda, un_opyoneda, opyon; intros f.
  refine ((isnat alpha f (Id a))^ @ _).
  cbn.
  apply ap.
  exact (cat_idr_strong f).
Defined.

(** Specialization to "full-faithfulness" of the Yoneda embedding.  (In quotes because, again, incoherence means we can't recover the witness of naturality.)  *)
Definition opyon_cancel {A : Type} `{Is0Coh1Cat A} (a b : A)
  : (opyon a $--> opyon b) -> (b $-> a)
  := un_opyoneda a (opyon b).

Definition opyon1 {A : Type} `{Is0Coh1Cat A} (a : A) : Fun1 A Type
  := (opyon a ; is0coh1functor_opyon a).

(** We can also deduce "full-faithfulness" on equivalences. *)
(* TODO: update *)
(*
Definition opyon_equiv {A : Type} `{Is1Coh1Cat_Strong A}
           {eA : HasEquivs A} (a b : A)
  : (opyon1 a $<~> opyon1 b) -> (b $<~> a).
Proof.
  intros f.
  refine (cate_adjointify (f.1 a (Id a)) (f^-1$.1 b (Id b)) _ _);
    apply Htpy_path; pose proof (f.2); pose proof (f^-1$.2); cbn in *.
  - refine ((isnat (fun a => (f.1 a)^-1) (f.1 a (Id a)) (Id b))^ @ _); cbn.
    refine (_ @ cate_issect (f.1 a) (Id a)); cbn.
    apply ap.
    serapply cat_idr_strong.
  - refine ((isnat f.1 (f^-1$.1 b (Id b)) (Id a))^ @ _); cbn.
    refine (_ @ cate_isretr (f.1 b) (Id b)); cbn.
    apply ap.
    serapply cat_idr_strong.
Defined.
*)

(** ** The contravariant Yoneda lemma *)

(** We can deduce this from the covariant version with some boilerplate. *)

Definition yon {A : Type} `{Is0Coh1Cat A} (a : A) : A^op -> Type
  := @opyon (A^op) _ a.

Global Instance is0coh1functor_yon {A : Type} `{Is0Coh1Cat A} (a : A)
  : Is0Coh1Functor (yon a)
  := @is0coh1functor_opyon A _ a.

Definition yoneda {A : Type} `{Is0Coh1Cat A} (a : A)
           (F : A^op -> Type) {ff : Is0Coh1Functor F}
  : F a -> (yon a $--> F)
  := @opyoneda (A^op) _ a F _.

Definition un_yoneda {A : Type} `{Is0Coh1Cat A} (a : A)
           (F : A^op -> Type) {ff : Is0Coh1Functor F}
  : (yon a $--> F) -> F a
  := @un_opyoneda (A^op) _ a F _.

Global Instance is1natural_yoneda {A : Type} `{Is0Coh2Cat A} (a : A)
       (F : A^op -> Type) {ff : Is0Coh1Functor F} {ff1 : Is1Coh1Functor F} (x : F a)
  : Is1Natural (yon a) F (yoneda a F x)
  := @is1natural_opyoneda (A^op) _ _ a F _ _ x.

Definition yoneda_issect {A : Type} `{Is0Coh2Cat A} (a : A) (F : A^op -> Type) {ff : Is0Coh1Functor F} {ff1 : Is1Coh1Functor F} (x : F a)
  : un_yoneda a F (yoneda a F x) = x
  := @opyoneda_issect (A^op) _ _ a F _ _ x.

Definition yoneda_isretr {A : Type}
           `{Is1Coh1Cat_Strong A} {ac2 : Is0Coh2Cat A} (a : A)
           (F : A^op -> Type) {ff : Is0Coh1Functor F} {ff1 : Is1Coh1Functor F}
           (alpha : yon a $--> F) {alnat : Is1Natural (yon a) F alpha}
           (b : A)
  : yoneda a F (un_yoneda a F alpha) b $== alpha b
  := @opyoneda_isretr A^op _ _ _ a F _ _ alpha alnat b.

Definition yon_cancel {A : Type} `{Is0Coh1Cat A} (a b : A)
  : (yon a $--> yon b) -> (a $-> b)
  := un_yoneda a (yon b).

Definition yon1 {A : Type} `{Is0Coh1Cat A} (a : A) : Fun1 A^op Type
  := opyon1 a.

(* TODO: update *)
(*
Definition yon_equiv {A : Type} `{Is1Coh1Cat_Strong A}
  {eA : HasEquivs A} (a b : A)
  : (yon1 a $<~> yon1 b) -> (a $<~> b)
  := (@opyon_equiv A^op _ _ _ _ a b).
*)

(** ** Wild category of wild categories *)

Record WildCat :=
{
  cat_carrier : Type;
  cat_is0coh1cat : Is0Coh1Cat cat_carrier;
  (* TODO: How much should we include here? *)
}.

Coercion cat_carrier : WildCat >-> Sortclass.
Global Existing Instance cat_is0coh1cat.

Global Instance is0coh1cat_wildcat : Is0Coh1Cat WildCat.
Proof.
  refine (Build_Is0Coh1Cat WildCat (fun A B => Fun1 A B) _ _).
Admitted.

Global Instance is0coh2cat_wildcat : Is0Coh2Cat WildCat.
Proof.
Admitted.

(* TODO: is1coh1cat_wildcat *)

(** ** Grothendieck constructions *)

(* How much coherence do we need? *)

(** ** Indexed product of categories *)

Global Instance is0coh1cat_forall (A : Type) (B : A -> Type)
  {c : forall a, Is0Coh1Cat (B a)}
  : Is0Coh1Cat (forall a, B a).
Proof.
  serapply Build_Is0Coh1Cat.
  + intros x y; exact (forall (a : A), x a $-> y a).
  + intros x a; exact (Id (x a)).
  + intros x y z f g a; exact (f a $o g a).
Defined.

Global Instance is0coh2cat_forall (A : Type) (B : A -> Type)
  {c1 : forall a, Is0Coh1Cat (B a)} {c2 : forall a, Is0Coh2Cat (B a)}
  : Is0Coh2Cat (forall a, B a).
Proof.
  serapply Build_Is0Coh2Cat.
  + intros x y f g; exact (forall a, f a $== g a).
  + intros x y f a; apply Id_Htpy.
  + intros x y f g p a; apply Opp_Htpy, p.
  + intros x y f g h p q a; exact (p a $@ q a).
  + intros x y z f g h p a; apply WhiskerL_Htpy, p.
  + intros x y z f g p h a; apply WhiskerR_Htpy, p.
Defined.

Global Instance is1coh1cat_forall (A : Type) (B : A -> Type)
    {c1 : forall a, Is0Coh1Cat (B a)} {c2 : forall a, Is0Coh2Cat (B a)}
    {c3 : forall a, Is1Coh1Cat (B a)}
    : Is1Coh1Cat (forall a, B a).
Proof.
  serapply Build_Is1Coh1Cat.
  + intros w x y z f g h a; apply cat_assoc.
  + intros x y f a; apply cat_idl.
  + intros x y f a; apply cat_idr.
Defined.


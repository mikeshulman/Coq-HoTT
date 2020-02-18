(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.

(** * Coinductive wild oo-categories *)

(** ** Globular types *)

(** Note that this is a "negative coinductive type", defined like a record with "fields" (i.e. destructors) rather than with a constructor (although it does still *have* a constructor, like a record does).  Negative coinductive types (new in Coq 8.9) make much more sense both syntactically and semantically than the previous "positive" version and should be used exclusively in new code.  It seems that here [A] functions like a "non-uniform parameter", although a negative coinductive type cannot have "indices" like an inductive type. *)
CoInductive IsGlob@{u} (A : Type@{u}) : Type :=
{
  Hom : A -> A -> Type@{u} ;
  isglob_hom : forall (x y : A), IsGlob (Hom x y) ;
}.
(* Technically this definition could allow two universe parameters, [A : Type@{u1}] and [Hom a b : Type@{u0}] with u0 <= u1.  But nearly all subsequent definitions force [u0 = u1].  Moreover, curiously, allowing [u0 != u1] here causes [iscat0_type] to fail with a universe error, while forcing [u0 = u1] here allows [iscat0_type] to succeed.  I don't fully understand why that is. *)

Existing Class IsGlob.
Arguments Hom {A _} a b.
Notation "a $-> b" := (Hom a b).
Global Existing Instance isglob_hom.

(** Every type is a globular type with its tower of identity types. *)
CoFixpoint isglob_withpaths (A : Type) : IsGlob A.
Proof.
  exists (@paths A); intros.
  apply isglob_withpaths.
Defined.

(** We could make this a global but low-priority instance, but doing so seems to break stuff later. *)
(* Global Existing Instance isglob_withpaths | 1000. *)

(** [forall] preserves globular types. *)
CoFixpoint isglob_forall (A : Type) (B : A -> Type) `(forall a, IsGlob (B a))
  : IsGlob (forall a, B a).
Proof.
  exists (fun f g => forall a, f a $-> g a); intros.
  rapply isglob_forall.
Defined.

Global Existing Instance isglob_forall.

(** Combining these, we can show that the universe is a globular type with functions, homotopies, and higher homotopies. *)
Global Instance isglob_type : IsGlob Type
  := Build_IsGlob _ (fun A B => A -> B) (fun A B => isglob_forall A (const B) (fun _ => isglob_withpaths B)).


(** ** Dependent/displayed globular types *)

CoInductive IsDGlob {A : Type@{u}} (B : A -> Type@{u}) `{IsGlob A} : Type :=
{
  DHom : forall (a b : A) (f : a $-> b) (u : B a) (v : B b), Type@{u} ;
  isdglob_dhom : forall (a b : A) (u : B a) (v : B b), @IsDGlob (a $-> b) (fun f => DHom a b f u v) _ ;
}.

Existing Class IsDGlob.
Arguments DHom {A B _ _ a b} f u v.
(** Since [DHom] has three arguments that generally need to be given explicitly, we can't really give it an infix notation. *)
Global Existing Instance isdglob_dhom.

(** Constant families of globular types are dependently globular. *)
CoFixpoint constant_dglob {A B : Type} `{IsGlob A} `{IsGlob B} : IsDGlob (@const A Type B).
Proof.
  unshelve econstructor.
  - intros ? ? ? u v; exact (u $-> v).
  - intros; rapply constant_dglob.
Defined.

Global Existing Instance constant_dglob.


(** ** Sigma globular types *)

CoFixpoint isglob_sigma {A} {B : A -> Type} `{IsDGlob A B}
  : IsGlob (sig B).
Proof.
  unshelve econstructor.
  - intros [a u] [b v]; exact { f : a $-> b & DHom f a b }.
  - intros [a u] [b v]; exact _.
Defined.

Global Existing Instance isglob_sigma.


(** ** Sections of dependent globular types, i.e. dependent 0-functors *)

CoInductive IsCatSect0 {A : Type} {B : A -> Type} `{IsDGlob A B} (F : forall a, B a) : Type :=
{
  fmapD : forall (a b : A) (f : a $-> b), DHom f (F a) (F b) ;
  iscatsect0_fmapD : forall (a b : A), @IsCatSect0 (a $-> b) (fun f => DHom f (F a) (F b)) _ _ (fmapD a b) ;
}.

Existing Class IsCatSect0.
Arguments fmapD {_ _ _ _} F {_ a b} f.
Global Existing Instance iscatsect0_fmapD.


(** ** 0-coherent oo-functors, i.e. globular morphisms *)

(** Just as non-dependent functions are a special case of dependent ones, ordinary functors are definitionally a special case of sections of displayed categories.  But it's convenient to make them syntactically distinct. *)

(*
CoInductive IsFunctor0 {A B : Type} `{IsGlob A} `{IsGlob B} (F : A -> B) : Type :=
{
  fmap : forall (a b : A), (a $-> b) -> (F a $-> F b) ;
  isfunctor0_fmap : forall (a b : A), @IsFunctor0 (a $-> b) (F a $-> F b) _ _ (fmap a b) ;
}.

Existing Class IsFunctor0.
Arguments fmap {_ _ _ _} F {_ a b} f.
Global Existing Instance isfunctor0_fmap.
*)

Class IsFunctor0 {A B : Type} `{IsGlob A} `{IsGlob B} (F : A -> B) :=
  iscatsect0_isfunctor0 : @IsCatSect0 A (const B) _ _ F.
Global Existing Instance iscatsect0_isfunctor0.

(** This is a syntactic variant of [Build_IsCatSect0] for non-dependent functors that leaves its coinductive goal written in terms of [IsFunctor0] instead of [IsCatSect0].  Unfortunately, it is not officially a "constructor" of [IsFunctor0], so tactics like [econstructor] won't use it. *)
Definition Build_IsFunctor0 {A B : Type} `{IsGlob A} `{IsGlob B} (F : A -> B)
           (fmap' : forall (a b : A), (a $-> b) -> (F a $-> F b))
           (isfunctor0_fmap' : forall (a b : A), IsFunctor0 (fmap' a b))
  : IsFunctor0 F
  := Build_IsCatSect0 _ _ _ _ F fmap' isfunctor0_fmap'.

Definition fmap {A B : Type} `{IsGlob A} `{IsGlob B} (F : A -> B) `{!IsFunctor0 F}
           {a b : A} (f : a $-> b)
  : F a $-> F b
  := fmapD F f.

Global Instance isfunctor0_fmap
       {A B : Type} `{IsGlob A} `{IsGlob B} (F : A -> B) `{!IsFunctor0 F} {a b : A}
  : @IsFunctor0 (a $-> b) (F a $-> F b) _ _ (@fmap _ _ _ _ F _ a b)
  := iscatsect0_fmapD F _ a b.

CoFixpoint isfunctor0_idmap {A : Type} `{IsGlob A}
  : @IsFunctor0 A A _ _ idmap.
Proof.
  refine (Build_IsFunctor0 _ _ _).
Defined.

CoFixpoint isfunctor0_compose {A B C : Type} `{IsGlob A} `{IsGlob B} `{IsGlob C}
       (G : B -> C) `{!IsFunctor0 G} (F : A -> B) `{!IsFunctor0 F}
  : IsFunctor0 (G o F).
Proof.
  unshelve econstructor.
  - intros a b; exact (fmap G o @fmap _ _ _ _ F _ a b).
  - intros a b; cbn. 
    exact (isfunctor0_compose _ _ _ _ _ _ (fmap G) _ (fmap F) _).
Defined.

Global Existing Instances isfunctor0_idmap isfunctor0_compose.

(** TODO: The next three should probably be generalized to sections. *)

(** Any function is a 0-coherent oo-functor between types equipped with their globular tower of identity types.  As for [isglob_withpaths], we don't make this an [Instance]. *)
CoFixpoint isfunctor0_withpaths (A B : Type) (F : A -> B)
  : @IsFunctor0 A B (isglob_withpaths A) (isglob_withpaths B) F.
Proof.
  refine (Build_IsFunctor0 F _ _).
  exact (@ap A B F).
  (** The coinductive assumption is found by typeclass search. *)
Defined.

(** Postcomposing and precomposing between [forall] types preserves 0-coherent oo-functors. *)
CoFixpoint isfunctor0_postcompose (A : Type)
           (B C : A -> Type) `{forall a, IsGlob (B a)} `{forall a, IsGlob (C a)}
           (F : forall a, B a -> C a) `{!forall a, IsFunctor0 (F a)}
  : @IsFunctor0 _ _ (isglob_forall A B _) (isglob_forall A C _) (fun f a => F a (f a)).
Proof.
  unshelve econstructor.
  - cbn; intros f g p a.
    exact (fmap (F a) (p a)).
  - intros; rapply isfunctor0_postcompose.
Defined.

CoFixpoint isfunctor0_precompose (A B : Type) (h : A -> B)
           (C : B -> Type) `{forall a, IsGlob (C a)}
  : @IsFunctor0 _ _ (isglob_forall B C _) (isglob_forall A (C o h) _) (fun f a => f (h a)).
Proof.
  unshelve econstructor.
  - cbn; intros f g p a.
    exact (p (h a)).
  - intros; rapply isfunctor0_precompose.
Defined.

Global Existing Instances isfunctor0_postcompose isfunctor0_precompose.


(** ** Dependent 0-coherent functors *)

(** These could alternatively be defined as sections of [B2] pulled back to [sig B1].  Conversely, a section of [B : A -> Type] could be defined as a dependent functor from [const Unit] to [B] over [idmap]. *)
CoInductive IsDFunctor0 {A1 A2 : Type} {B1 : A1 -> Type} {B2 : A2 -> Type}
      `{IsDGlob A1 B1} `{IsDGlob A2 B2}
      (F : A1 -> A2) `{!IsFunctor0 F} (G : forall a:A1, B1 a -> B2 (F a)) :=
{
  dfmap : forall (a b : A1) (u : B1 a) (v : B1 b) (f : a $-> b),
    DHom f u v -> DHom (fmap F f) (G a u) (G b v) ;
  isdfunctor0_dfmap : forall (a b : A1) (u : B1 a) (v : B1 b),
      @IsDFunctor0 _ _ _ _ _ _ _ _ (fmap F) _ (dfmap a b u v) ;
}.

Existing Class IsDFunctor0.
Arguments dfmap {A1 A2 B1 B2 _ _ _ _} F {_} G {_ a b u v f} p.
Global Existing Instance isdfunctor0_dfmap.


(** ** Pullback of dependent globular types *)

CoFixpoint isdglob_compose {A1 A2 : Type} (B : A2 -> Type)
           `{IsGlob A1} `{IsDGlob A2 B}
           (F : A1 -> A2) `{!IsFunctor0 F}
  : IsDGlob (B o F).
Proof.
  unshelve econstructor.
  - intros a b f u v; exact (DHom (fmap F f) u v).
  - intros a b u v. 
    refine (isdglob_compose _ (F a $-> F b) (fun g => DHom g u v)
                            _ _ _ (fmap F) _).
Defined.


(** ** 0-coherent oo-categories *)

(** The implicit oo-category convention is in effect: "IsCat" means "is an oo-category", where by oo-category we mean an (oo,oo)-category.  The postfix "0" means "0-coherent", i.e. equipped with all the *operations* but no coherence. *)
CoInductive IsCat0 (A : Type) `{IsGlob A} : Type :=
{
  cat_id : forall (a : A), a $-> a ;
  cat_comp : forall (a b c : A), (b $-> c) -> (a $-> b) -> (a $-> c) ;
  isfunctor0_postcomp : forall (a b c : A) (g : b $-> c), IsFunctor0 (fun f => cat_comp a b c g f) ;
  isfunctor0_precomp : forall (a b c : A) (f : a $-> b), IsFunctor0 (fun g => cat_comp a b c g f) ;
  iscat0_hom : forall (a b : A), @IsCat0 (a $-> b) _ ;
}.

Existing Class IsCat0.
Arguments cat_id {A _ _} a.
Arguments cat_comp {A _ _ a b c} g f.
Notation "g $o f" := (cat_comp g f).
Global Existing Instances isfunctor0_postcomp isfunctor0_precomp iscat0_hom.

Definition cat_postcomp {A : Type} `{IsCat0 A}
           (a : A) {b c : A} (g : b $-> c)
  : (a $-> b) -> (a $-> c)
  := fun f => g $o f.

Definition cat_precomp {A : Type} `{IsCat0 A}
           {a b : A} (c : A) (f : a $-> b)
  : (b $-> c) -> (a $-> c)
  := fun g => g $o f.

(* These seem to be unnecessary; I guess [cat_postcomp] and [cat_precomp] are sufficiently transparent to typeclass search. *)
(*
Global Instance isfunctor0_postcomp {A : Type} `{IsGlob A} {ac : IsCat0 A}
       {a b c : A} (g : b $-> c)
  : IsFunctor0 (cat_postcomp a g).
Proof. destruct ac as [? ? gc ? ?]; exact (gc a b c g). Defined.

Global Instance isfunctor0_precomp {A : Type} `{IsGlob A} {ac : IsCat0 A}
       {a b c : A} (f : a $-> b)
  : IsFunctor0 (cat_precomp c f).
Proof. destruct ac as [? ? ? gc ?]; exact (gc a b c f). Defined.
*)

Definition cat_postwhisker {A} `{IsCat0 A} {a b c : A}
           {f g : a $-> b} (h : b $-> c) (p : f $-> g)
  : h $o f $-> h $o g
  := fmap (cat_postcomp a h) p.
Notation "h $<o p" := (cat_postwhisker h p) (at level 30).

Definition cat_prewhisker {A} `{IsCat0 A} {a b c : A}
           {f g : b $-> c} (p : f $-> g) (h : a $-> b)
  : f $o h $-> g $o h
  := fmap (cat_precomp c h) p.
Notation "p $o> h" := (cat_prewhisker p h) (at level 30).

(** The tower of identity types is a 0-coherent oo-category with path composition.  Again, not an [Instance]. *)
CoFixpoint iscat0_withpaths (A : Type) : @IsCat0 A (isglob_withpaths A).
Proof.
  unshelve econstructor.
  - intros a b c p q; exact (q @ p).
  - intros a; exact idpath.
  - intros; apply isfunctor0_withpaths.
  - intros; apply isfunctor0_withpaths.
  - intros; apply iscat0_withpaths.
Defined.

(** [forall] preserves 0-coherent oo-categories. *)
CoFixpoint iscat0_forall (A : Type) (B : A -> Type)
           {bg : forall a, IsGlob (B a)} {bc : forall a, IsCat0 (B a)}
  : @IsCat0 (forall a, B a) (isglob_forall A B _).
Proof.
  unshelve econstructor; cbn.
  - intros f g h q p a; exact (q a $o p a).
  - intros f a; exact (cat_id (f a)).
  - intros; rapply isfunctor0_postcompose.
  - intros f g h p; rapply isfunctor0_postcompose.
  - intros; rapply iscat0_forall.
Defined.

(** And combining these, the universe is a 0-coherent oo-category. *)
Global Instance iscat0_type : IsCat0 Type.
Proof.
  unshelve econstructor.
  - intros A B C g f; exact (g o f).
  - intros A; exact idmap.
  - intros A B C g; cbn.
    apply isfunctor0_postcompose.
    intros; apply isfunctor0_withpaths.
  - intros A B C f; cbn.
    rapply isfunctor0_precompose.
  - intros A B.
    rapply iscat0_forall. 
    intros; rapply iscat0_withpaths.
Defined.

Global Existing Instances iscat0_forall iscat0_type.


(** ** Displayed 0-coherent oo-categories *)

CoInductive IsDCat0 {A : Type} (B : A -> Type) `{IsCat0 A} `{!IsDGlob B} : Type :=
{
  dcat_id : forall (a : A) (u : B a), DHom (cat_id a) u u ;
  dcat_comp : forall (a b c : A) (u : B a) (v : B b) (w : B c)
                     (g : b $-> c) (f : a $-> b),
      DHom g v w -> DHom f u v -> DHom (g $o f) u w ;
  isdfunctor0_postcomp : forall (a b c : A) (u : B a) (v : B b) (w : B c)
                                (g : b $-> c) (q : DHom g v w),
      IsDFunctor0 (fun f => g $o f) (fun f p => dcat_comp a b c u v w g f q p) ;
  isdfunctor0_precomp : forall (a b c : A) (u : B a) (v : B b) (w : B c)
                              (f : a $-> b) (p : DHom f u v),
      IsDFunctor0 (fun g => g $o f) (fun g q => dcat_comp a b c u v w g f q p) ;
  isdcat0_dhom : forall (a b : A) (u : B a) (v : B b), @IsDCat0 (a $-> b) (fun f => DHom f u v) _ _ _ ;
}.

Existing Class IsDCat0.
Arguments dcat_id {A B _ _ _ _ a} u.
Arguments dcat_comp {A B _ _ _ _ a b c u v w g f} q p.
Notation "q $oD p" := (dcat_comp q p) (at level 30).
Global Existing Instances isdfunctor0_postcomp isdfunctor0_precomp isdcat0_dhom.

Definition dcat_postcomp {A : Type} {B : A -> Type} `{IsDCat0 A B}
           {a b c : A} (u : B a) {v : B b} {w : B c}
           {g : b $-> c} (f : a $-> b) (q : DHom g v w)
  : DHom f u v -> DHom (g $o f) u w
  := fun p => q $oD p.

Definition dcat_precomp {A : Type} {B : A -> Type} `{IsDCat0 A B}
           {a b c : A} {u : B a} {v : B b} (w : B c)
           (g : b $-> c) {f : a $-> b} (p : DHom f u v)
  : DHom g v w -> DHom (g $o f) u w
  := fun q => q $oD p.

Definition dcat_postwhisker {A : Type} {B : A -> Type} `{IsDCat0 A B}
           {a b c : A} {u : B a} {v : B b} {w : B c}
           {f g : a $-> b} {h : b $-> c} {p : f $-> g}
           {f' : DHom f u v} {g' : DHom g u v} (h' : DHom h v w) (p' : DHom p f' g')
  : DHom (h $<o p) (h' $oD f') (h' $oD g')
  := dfmap (cat_postcomp a h) (fun k => dcat_postcomp u k h') p'.
Notation "h' $<oD p'" := (dcat_postwhisker h' p') (at level 30).

Definition dcat_prewhisker {A : Type} {B : A -> Type} `{IsDCat0 A B}
           {a b c : A} {u : B a} {v : B b} {w : B c}
           {f g : b $-> c} {p : f $-> g} {h : a $-> b}
           {f' : DHom f v w} {g' : DHom g v w} (p' : DHom p f' g') (h' : DHom h u v)
  : DHom (p $o> h) (f' $oD h') (g' $oD h')
  := dfmap (cat_precomp c h) (fun k => dcat_precomp w k h') p'.
Notation "p $o>D h" := (cat_prewhisker p h) (at level 30).

(** TODO: Examples.  For instance, any dependent type should be a displayed 0-coherent oo-category with its tower of dependent identity types, and so on.  Also, [pType] should be displayed over [Type]. *)


(** ** Quasi-isomorphisms *)

(** A morphism in an (oo,oo)-category is an equivalence if and only if there is a morphism backwards such that both composites are equivalent to identities.  

Since the notion of equivalence appears on both sides of this statement, it is not immediately a definition.  If we interpret it inductively, then in order to get something meaningful (and in particular nonempty) we need to additionally assume a lot of other stuff, basically amounting to the statement that the equivalences themselves form an oo-category, which is not very practical.  Or we can interpret the equivalences as extra data that are merely assumed to satisfy this statement, but in that case we also need to assume at least that the equivalences are closed under composition (to prove from this statement that n-equivalences are closed under composition, we need to know that (n+1)-equivalences are, so the induction has no bottom).  Thus, it is simplest to interpret this statement coinductively, in which case it produces a useful and meaningful "largest" class of equivalences.

Note that in an (oo,n)-category for finite n, there is no difference in the notions of "equivalence" resulting from all these approaches.  Since this covers the vast majority of cases arising in practice, and in fact very few examples of (oo,oo)-categories are known that are not (oo,n)-categories for some finite n, it is reasonable to take the convenient coinductive characterization of equivalences.

This coinductive definition of "equivalence" is not itself coherent (i.e. the resulting type "f is an equivalence" is not a proposition), so we give it the more derogatory name "quasi-isomorphism". *)

CoInductive IsQIso {A : Type} `{IsCat0 A} {a b : A} (f : a $-> b) : Type :=
{
  qiso_inv : b $-> a ;
  qiso_issect : qiso_inv $o f $-> cat_id a ;
  qiso_isretr : f $o qiso_inv $-> cat_id b ;
  isqiso_issect : @IsQIso (a $-> a) _ _ _ _ qiso_issect ;
  isqiso_isretr : @IsQIso (b $-> b) _ _ _ _ qiso_isretr ;
}.

Existing Class IsQIso.
Arguments qiso_inv {A _ _ a b} f {_}.
Arguments qiso_issect {A _ _ a b} f {_}.
Arguments qiso_isretr {A _ _ a b} f {_}.
Global Existing Instances isqiso_issect isqiso_isretr.

(** We don't even need coinduction to show that the inverse of a quasi-isomorphism is a quasi-isomorphism. *)
Global Instance isqiso_inv {A : Type} `{IsCat0 A}
       {a b : A} (f : a $-> b) `{!IsQIso f}
  : IsQIso (qiso_inv f).
Proof.
  unshelve econstructor.
  - exact f.
  - serapply qiso_isretr.
  - serapply qiso_issect.
  - exact _.
  - exact _.
Defined.

(** Every path is a quasi-isomorphism. *)
CoFixpoint isqiso_withpaths {A : Type} {a b : A} (p : a = b)
  : @IsQIso A _ (iscat0_withpaths A) a b p.
Proof.
  unshelve econstructor.
  - exact (p^).
  - cbn. apply concat_pV.
  - cbn. apply concat_Vp.
  - apply isqiso_withpaths.
  - apply isqiso_withpaths.
Defined.

(** And a pointwise quasi-isomorphism in a [forall] is a quasi-isomorphism. *)
CoFixpoint isqiso_forall (A : Type) (B : A -> Type)
           {bg : forall a, IsGlob (B a)} {bc : forall a, IsCat0 (B a)}
           (f g : forall a, B a) (p : @Hom _ (isglob_forall A B _) f g) `{forall a, IsQIso (p a)}
  : @IsQIso _ _ (iscat0_forall A B) f g p.
Proof.
  unshelve econstructor.
  - exact (fun a => qiso_inv (p a)).
  - cbn; intros a. exact (qiso_issect (p a)).
  - cbn; intros a. exact (qiso_isretr (p a)).
  - rapply isqiso_forall. intros; exact (isqiso_issect (p a) _).
  - rapply isqiso_forall. intros; exact (isqiso_isretr (p a) _).
Defined.

Global Existing Instance isqiso_forall.


(** ** oo-categories with equivalences  *)

(** It is unclear whether it is possible to *define*, in the finite syntax of type theory, a coherent notion of equivalence in an arbitrary (oo,oo)-category that is logically equivalent to quasi-isomorphism.  However, we can say what it means for a particular oo-category to be equipped with such a notion.  This is more useful in practice anyway, since usually there is an already-extant coherent notion of equivalence (e.g. [IsEquiv] for [Type]) that we want to use wild categories to talk about.

For the present, we don't assert that the notion of equivalence *is* coherent, only that it is logically equivalent to quasi-isomorphism.  It could be that in the future we want to add this assumption, or it could be that we will want to include some "truly wild" examples in which it is not actually coherent. *)

CoInductive HasEquivs (A : Type) `{IsCat0 A} :=
{
  CatEquiv' : A -> A -> Type where "a $<~> b" := (CatEquiv' a b);
  CatIsEquiv' : forall (a b : A), (a $-> b) -> Type;
  cate_fun' : forall (a b : A), (a $<~> b) -> (a $-> b);
  cate_isequiv' : forall (a b : A) (f : a $<~> b), CatIsEquiv' a b (cate_fun' a b f);
  cate_buildequiv' : forall (a b : A) (f : a $-> b), CatIsEquiv' a b f -> CatEquiv' a b;
  cate_buildequiv_fun' : forall (a b : A) (f : a $-> b) (fe : CatIsEquiv' a b f),
      cate_fun' a b (cate_buildequiv' a b f fe) $-> f;
  isqiso_cate_buildequiv_fun' : forall (a b : A) (f : a $-> b) (fe : CatIsEquiv' a b f),
      IsQIso (cate_buildequiv_fun' a b f fe);
  isqiso_catie' : forall (a b : A) (f : a $-> b), CatIsEquiv' a b f -> IsQIso f;
  catie_isqiso : forall (a b : A) (f : a $-> b), IsQIso f -> CatIsEquiv' a b f;
  hasequivs_hom : forall (a b : A), @HasEquivs (a $-> b) _ _;
}.

Existing Class HasEquivs.
Global Existing Instances isqiso_catie' isqiso_cate_buildequiv_fun' hasequivs_hom.

(** Since apparently a field of a record can't be the source of a coercion (Coq complains about the uniform inheritance condition, although as officially stated that condition appears to be satisfied), we redefine all the fields of [HasEquivs]. *)

Definition CatEquiv {A} `{HasEquivs A} (a b : A)
  := @CatEquiv' A _ _ _ a b.

Notation "a $<~> b" := (CatEquiv a b).
Arguments CatEquiv : simpl never.

(** I'm not sure what to do about notation.  It would be nice to be able to use the [f $== g] notation for [f $<~> g] when [f] and [g] belong to a hom-type, perhaps only in an (oo,1)-category, with the diagrammatic-order operations [p $@ q] and so on.  But I'm not sure how to declare such notations and restrict it to that case. *)

Definition cate_fun {A} `{HasEquivs A} {a b : A} (f : a $<~> b)
  : a $-> b
  := @cate_fun' A _ _ _ a b f.

Coercion cate_fun : CatEquiv >-> Hom.

(* Being an equivalence should be a typeclass, but we have to redefine it to work around https://github.com/coq/coq/issues/8994 . *)
Class CatIsEquiv {A} `{HasEquivs A} {a b : A} (f : a $-> b)
  := catisequiv : CatIsEquiv' A _ a b f.

Global Instance cate_isequiv {A} `{HasEquivs A} {a b : A} (f : a $<~> b)
  : CatIsEquiv f
  := cate_isequiv' A _ a b f.

Global Instance isqiso_catie {A} `{HasEquivs A} {a b : A}
       (f : a $-> b) {fe : CatIsEquiv f}
  : IsQIso f.
Proof.
  rapply isqiso_catie'; assumption.
Defined.

Definition Build_CatEquiv {A} `{HasEquivs A} {a b : A}
           (f : a $-> b) {fe : CatIsEquiv f}
  : a $<~> b
  := cate_buildequiv' A _ a b f fe.

Definition catie_adjointify {A} `{HasEquivs A} {a b : A}
           (f : a $-> b) (g : b $-> a)
           (r : f $o g $<~> cat_id b) (s : g $o f $<~> cat_id a)
  : CatIsEquiv f.
Proof.
  apply catie_isqiso.
  exact (Build_IsQIso _ _ _ _ _ f g s r _ _).
Defined.

Definition cate_adjointify {A} `{HasEquivs A} {a b : A}
           (f : a $-> b) (g : b $-> a)
           (r : f $o g $<~> cat_id b) (s : g $o f $<~> cat_id a)
  : a $<~> b
  := @Build_CatEquiv _ _ _ _ a b f (catie_adjointify f g r s).

Definition cate_inv {A} `{HasEquivs A} {a b : A} (f : a $<~> b) : b $<~> a.
Proof.
  serapply (Build_CatEquiv (qiso_inv f)); try exact _.
  rapply catie_isqiso.
Defined.

Notation "f ^-1$" := (cate_inv f).

Global Instance symmetric_cate {A} `{HasEquivs A}
  : Symmetric (@CatEquiv A _ _ _)
  := fun a b f => cate_inv f.

Definition cate_buildequiv_fun {A} `{HasEquivs A} {a b : A}
           (f : a $-> b) {fe : CatIsEquiv f}
  : cate_fun (Build_CatEquiv f) $<~> f.
Proof.
  serapply (Build_CatEquiv (cate_buildequiv_fun' A _ _ _ f _)); try exact _.
  apply catie_isqiso, isqiso_cate_buildequiv_fun'.
Defined.

(** In order to prove that quasi-isomorphisms, hence also equivalences, are closed under composition and functorial action (including whiskering), we will need the categories to be 1-coherent. *)


(** ** 1-coherent oo-functors *)

CoInductive IsFunctor1 {A B : Type} `{IsCat0 A} `{HasEquivs B}
            (F : A -> B) {ff : IsFunctor0 F} : Type :=
{
  fmap_id : forall (a : A), fmap F (cat_id a) $<~> cat_id (F a) ;
  fmap_comp : forall (a b c : A) (f : a $-> b) (g : b $-> c),
      fmap F (g $o f) $<~> fmap F g $o fmap F f ;
  isfunctor1_fmap : forall (a b : A),
      @IsFunctor1 (a $-> b) (F a $-> F b) _ _ _ _ _ (@fmap _ _ _ _ F _ a b) _ ;
}.

Existing Class IsFunctor1.
Arguments fmap_id {A B _ _ _ _ _} F {_ _} a.
Arguments fmap_comp {A B _ _ _ _ _} F {_ _ a b c} f g.
Global Existing Instance isfunctor1_fmap.

(* TODO: Examples *)


(** ** 1-coherent oo-categories *)

(** There is more than one possible choice for the meaning of the numerical coherence index on a wild oo-category.  Here we take it to refer to the maximal difference in dimension between the inputs and outputs of operations, then a 1-coherent oo-category includes not just associators and unitors but also interchangors, while a 2-coherent one includes pentagonator and triangulator and also Gray-category-like coherences for the interchangor.

Another possibility would be for a 1-coherent oo-category to only include enough data to "look like a wild 1-category" at each dimension, in which case the interchangors wouldn't appear until the 2-coherent level.  It's not clear to me at the moment which choice is better. *)
CoInductive IsCat1 (A : Type) `{HasEquivs A} : Type :=
{
  cat_assoc : forall (a b c d : A) (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f $<~> h $o (g $o f) ;
  cat_idl : forall (a b : A) (f : a $-> b), cat_id b $o f $<~> f ;
  cat_idr : forall (a b : A) (f : a $-> b), f $o cat_id a $<~> f ;
  cat_interchange : forall (a b c : A) (f1 f2 : a $-> b) (g1 g2 : b $-> c) (p : f1 $-> f2) (q : g1 $-> g2),
      ((q $o> f2) $o (g1 $<o p)) $<~> ((g2 $<o p) $o (q $o> f1)) ;
  isfunctor1_postcomp : forall (a b c : A) (g : b $-> c), IsFunctor1 (cat_postcomp a g) ;
  isfunctor1_precomp : forall (a b c : A) (f : a $-> b), IsFunctor1 (cat_precomp c f) ;
  iscat1_hom : forall (a b : A), @IsCat1 (a $-> b) _ _ _ ;
}.

Existing Class IsCat1.
Arguments cat_assoc {A _ _ _ _ a b c d} f g h.
Arguments cat_idl {A _ _ _ _ a b} f.
Arguments cat_idr {A _ _ _ _ a b} f.
Arguments cat_interchange {A _ _ _ _ a b c f1 f2 g1 g2} p q.
Global Existing Instances isfunctor1_postcomp isfunctor1_precomp iscat1_hom.

Definition cat_assoc_opp {A : Type} `{IsCat1 A}
           {a b c d : A} (f : a $-> b) (g : b $-> c) (h : c $-> d)
  : h $o (g $o f) $<~> (h $o g) $o f
  := (cat_assoc f g h)^-1$.

Definition cat_interchange_opp {A : Type} `{IsCat1 A}
           {a b c : A} {f1 f2 : a $-> b} {g1 g2 : b $-> c} (p : f1 $-> f2) (q : g1 $-> g2)
  : ((g2 $<o p) $o (q $o> f1)) $<~> ((q $o> f2) $o (g1 $<o p))
  := (cat_interchange p q)^-1$.

(** Now we can prove that identity morphisms are equivalences. *)
Global Instance catie_id {A : Type} `{IsCat1 A} (a : A)
  : CatIsEquiv (cat_id a).
Proof.
  serapply catie_adjointify.
  - exact (cat_id a).
  - exact (cat_idl (cat_id a)).
  - exact (cat_idl (cat_id a)).
Defined.

Definition cate_id {A : Type} `{IsCat1 A} (a : A)
  : a $<~> a
  := Build_CatEquiv (cat_id a).

Global Instance reflexive_cate {A} `{IsCat1 A}
  : Reflexive (@CatEquiv A _ _ _)
  := cate_id.

(* TODO: Examples *)


(** ** Composing equivalences *)

(** We now intend to prove by mutual coinduction that quasi-isomorphisms are closed under composition in a 1-coherent oo-category and preserved by 1-coherent oo-functors, hence so are equivalences.  Unfortunately this is a bit more complicated than it ought to be.  The following proof is semantically correct, but Coq rejects it as ill-formed since its guardedness condition is overly simplistic, requiring that corecursive calls appear only directly in arguments of the constructor. *)
CoFixpoint isqiso_compose {A : Type} `{IsCat1 A} {a b c : A}
           (g : b $-> c) {gi : IsQIso g} (f : a $-> b) {fi : IsQIso f}
  : IsQIso (g $o f)
with isqiso_fmap {A B : Type} `{IsCat1 A} `{IsCat1 B}
               (F : A -> B) `{!IsFunctor0 F, !IsFunctor1 F}
               {a b : A} (f : a $-> b) `{!IsQIso f}
     : IsQIso (fmap F f).
Proof.
  { unshelve econstructor.
    - exact (qiso_inv f $o qiso_inv g).
    - refine (qiso_issect f $o _).
      refine ((qiso_inv f $<o (cat_idl f)) $o _).
      refine (_ $o cat_assoc _ _ _).
      refine (qiso_inv f $<o _).
      refine (_ $o cat_assoc_opp _ _ _).
      exact (qiso_issect g $o> f).
    - refine (qiso_isretr g $o _).
      refine (((cat_idr g) $o> qiso_inv g) $o _).
      refine (_ $o cat_assoc_opp _ _ _).
      refine (_ $o> qiso_inv g).
      refine (_ $o cat_assoc _ _ _).
      exact (g $<o qiso_isretr f).
    - rapply isqiso_compose.
      rapply isqiso_compose.
      rapply isqiso_compose.
      refine (isqiso_fmap _ _ _ _ _ _ _ _ _ _ (cat_postcomp a (qiso_inv f)) _ _ _ _ _ _); try exact _.
      rapply isqiso_compose.
      refine (isqiso_fmap _ _ _ _ _ _ _ _ _ _ (cat_precomp b f) _ _ _ _ _ _).
    - rapply isqiso_compose.
      rapply isqiso_compose.
      { refine (isqiso_fmap _ _ _ _ _ _ _ _ _ _ (cat_precomp c (qiso_inv g)) _ _ _ _ _ _). }
      rapply isqiso_compose.
      refine (isqiso_fmap _ _ _ _ _ _ _ _ _ _ (cat_precomp c (qiso_inv g)) _ _ _ _ _ _). }
  { unshelve econstructor.
    - exact (fmap F (qiso_inv f)).
    - refine (fmap_id F a $o _).
      refine (_ $o qiso_inv (fmap_comp F f (qiso_inv f))).
      apply fmap; try exact _.
      serapply qiso_issect.
    - refine (fmap_id F b $o _).
      refine (_ $o qiso_inv (fmap_comp F (qiso_inv f) f)).
      apply fmap; try exact _.
      serapply qiso_isretr.
    - refine (isqiso_compose _ _ _ _ _ _ _ _ _ _ _ _).
    - refine (isqiso_compose _ _ _ _ _ _ _ _ _ _ _ _). }
Fail Guarded.
Abort.

(** Thus, instead of a mutual coinduction over composition and functorial action, we prove in a single coinduction that "any operation built out of composition and functorial actions" preserves quasi-isomorphisms.  This requires a sort of quoting/reflection to specify what that means; we put it in a module since no one else should need to peek inside it, and so we don't have to worry about namespace conflicts. *)

Module QuoteQIso.

  (* Reflection for compound operations built out of composition and functors. *)
  Inductive Quotable {A : Type} `{IsCat1 A} : forall (x y : A), (x $-> y) -> Type :=
  | quote_unquote : forall (a b : A) (f : a $-> b), Quotable a b f
  | quote_comp : forall (a b c : A) (g : b $-> c) (f : a $-> b),
      Quotable b c g -> Quotable a b f -> Quotable a c (g $o f)
  | quote_fmap : forall (B : Type) (bg : IsGlob B) (bc0 : IsCat0 B) {bh : HasEquivs B} (bc1 : IsCat1 B)
                        (F : B -> A) (ff0 : IsFunctor0 F) (ff1 : IsFunctor1 F) (u v : B) (f : u $-> v),
      @Quotable B _ _ _ _ u v f -> Quotable (F u) (F v) (fmap F f).

  Arguments Quotable {A _ _ _ _ x y} f.
  Arguments quote_fmap {A _ _ _ _ _ _ _ _ _} F {_ _ _ _} f qf.
  Existing Class Quotable.

  (** This type is the statement that "all the inputs" of [f] are quasi-isomorphisms. *)
  Definition IsQQIso {A : Type} `{IsCat1 A} {x y : A} (f : x $-> y) {qf : Quotable f}
    : Type.
  Proof.
    induction qf as [? ? ? ? ? a b f|? ? ? ? ? a b c g f qg IHg qf IHf|? ? ? ? ? ? ? ? ? ? F ? ? u v f qf IHf].
    - exact (IsQIso f).
    - exact (IHg * IHf).
    - exact IHf.
  Defined.

  Existing Class IsQQIso.

  (** It's sometimes convenient to bundle these up.  An element of this type is a morphism together with a "reason that it's a quasi-isomorphism", i.e. a way in which it is built up from composition and functor actions out of known quasi-isomorphisms. *)
  Record QQIso {A : Type} `{IsCat1 A} (x y : A) :=
    {
      quotable_map : x $-> y ;
      quotable_quotablemap : Quotable quotable_map ;
      isqqiso_quotablemap : IsQQIso quotable_map ;
    }.

  Coercion quotable_map : QQIso >-> Hom.

  Definition quotable_inv {A : Type} `{IsCat1 A} {x y : A}
             (f : x $-> y) {qf : Quotable f} {qfi : IsQQIso f}
    : y $-> x.
  Proof.
    induction qf as [? ? ? ? ? a b f|? ? ? ? ? a b c g f qg IHg qf IHf|? ? ? ? ? ? ? ? ? ? F ? ? u v f qf IHf].
    - cbn in qfi.
      exact (qiso_inv f).
    - destruct qfi as [qgi qfi].
      exact ((IHf qfi) $o (IHg qgi)).
    - exact (fmap F (IHf qfi)).
  Defined.

  (** Now we can show directly (no coinduction required) that a bunch of operations preserve "witnessed quasi-isomorphisms".  *)

  Definition qqiso_compose {A : Type} `{IsCat1 A} {a b c : A}
             (g : QQIso b c) (f : QQIso a b)
    : QQIso a c.
  Proof.
    destruct f as [f qf qfi]; destruct g as [g qg qgi].
    unshelve econstructor.
    - exact (g $o f).
    - rapply quote_comp.
    - exact (qgi,qfi).
  Defined.

  Local Notation "g $oQ f" := (qqiso_compose g f) (at level 30).

  Definition qqiso_fmap {B A : Type} `{IsCat1 B} `{IsCat1 A}
             (F : B -> A) `{!IsFunctor0 F, !IsFunctor1 F} {u v : B} (f : QQIso u v)
    : QQIso (F u) (F v).
  Proof.
    destruct f as [f qf qfi].
    unshelve econstructor.
    - exact (fmap F f).
    - refine (quote_fmap F f _).
    - assumption.
  Defined.

  Local Notation "h $<oQ p" := (qqiso_fmap (cat_postcomp _ h) p) (at level 30).
  Local Notation "p $o>Q h" := (qqiso_fmap (cat_precomp _ h) p) (at level 30).

  Definition qqiso_assoc {A : Type} `{IsCat1 A} {a b c d : A}
             (f : a $-> b) (g : b $-> c) (h : c $-> d)
    : QQIso ((h $o g) $o f) (h $o (g $o f)).
  Proof. unshelve econstructor; [ exact (cat_assoc f g h) | apply quote_unquote | cbn; exact _ ]. Defined.

  Definition qqiso_assoc_opp {A : Type} `{IsCat1 A} {a b c d : A}
             (f : a $-> b) (g : b $-> c) (h : c $-> d)
    : QQIso (h $o (g $o f)) ((h $o g) $o f).
  Proof. unshelve econstructor; [ exact (cat_assoc_opp f g h) | apply quote_unquote | cbn; exact _ ]. Defined.

  Definition qqiso_idl {A : Type} `{IsCat1 A} {a b : A} (f : a $-> b)
    : QQIso (cat_id b $o f) f.
  Proof. unshelve econstructor; [ exact (cat_idl f) | apply quote_unquote | cbn; exact _ ]. Defined.

  Definition qqiso_idr {A : Type} `{IsCat1 A} {a b : A} (f : a $-> b)
    : QQIso (f $o cat_id a) f.
  Proof. unshelve econstructor; [ exact (cat_idr f) | apply quote_unquote | cbn; exact _ ]. Defined.

  Definition qqiso_fmap_id {A B : Type} `{IsCat1 A} `{IsCat1 B}
             (F : A -> B) `{!IsFunctor0 F, !IsFunctor1 F} (a : A)
    : QQIso (fmap F (cat_id a)) (cat_id (F a)).
  Proof. unshelve econstructor; [ exact (fmap_id F a) | apply quote_unquote | cbn; exact _ ]. Defined.

  Definition qqiso_fmap_comp {A B : Type} `{IsCat1 A} `{IsCat1 B}
             (F : A -> B) `{!IsFunctor0 F, !IsFunctor1 F}
             {a b c : A} (f : a $-> b) (g : b $-> c)
    : QQIso (fmap F (g $o f)) (fmap F g $o fmap F f).
  Proof. unshelve econstructor; [ exact (fmap_comp F f g) | apply quote_unquote | cbn; exact _ ]. Defined.

  Definition qqiso_fmap_comp_opp {A B : Type} `{IsCat1 A} `{IsCat1 B}
             (F : A -> B) `{!IsFunctor0 F, !IsFunctor1 F}
             {a b c : A} (f : a $-> b) (g : b $-> c)
    : QQIso (fmap F g $o fmap F f) (fmap F (g $o f)).
  Proof. unshelve econstructor; [ exact (qiso_inv (fmap_comp F f g)) | apply quote_unquote | cbn; exact _ ]. Defined.

  Existing Instances quotable_quotablemap isqqiso_quotablemap.

  (** The bundled approach, with these basic operations in place, now makes it fairly straightforward to prove that [issect] and [isretr] for a witnessed quasi-isomorphism are also witnessed quasi-isomorphisms. *)

  Definition quotable_issect {A : Type} `{IsCat1 A} {x y : A}
             (f : x $-> y) {qf : Quotable f} {qfi : IsQQIso f}
    : QQIso (quotable_inv f $o f) (cat_id x).
  Proof.
    induction qf as [? ? ? ? ? a b f|? ? ? ? ? a b c g f qg IHg qf IHf|? ? ? ? ? ? ? ? ? ? F ? ? u v f qf IHf].
    - simple notypeclasses refine (Build_QQIso _ _ _ _ _ _ _ _ _ _); cbn.
      + exact (qiso_issect f).
      + apply quote_unquote.
      + cbn. apply isqiso_issect.
    - destruct qfi as [qgi qfi].
      refine (_ $oQ qqiso_assoc _ _ _).
      refine ((IHf qfi) $oQ _).
      refine (quotable_inv f $<oQ _).
      refine (qqiso_idl f $oQ _). 
      exact (((IHg qgi) $o>Q f) $oQ qqiso_assoc_opp _ _ _).
    - refine (qqiso_fmap_id F u $oQ _).
      refine (qqiso_fmap (fmap F) (IHf qfi) $oQ _).
      exact ((qqiso_fmap_comp_opp F f (quotable_inv f))).
  Defined.

  Definition quotable_isretr {A : Type} `{IsCat1 A} {x y : A} (* (f : QQIso x y) *)
             (f : x $-> y) {qf : Quotable f} {qfi : IsQQIso f}
    : QQIso (f $o quotable_inv f) (cat_id y).
  Proof.
    induction qf as [? ? ? ? ? a b f|? ? ? ? ? a b c g f qg IHg qf IHf|? ? ? ? ? ? ? ? ? ? F ? ? u v f qf IHf].
    - simple notypeclasses refine (Build_QQIso _ _ _ _ _ _ _ _ _ _); cbn.
      + exact (qiso_isretr f).
      + apply quote_unquote.
      + cbn. apply isqiso_isretr.
    - destruct qfi as [qgi qfi].
      refine (_ $oQ qqiso_assoc_opp _ _ _).
      refine ((IHg qgi) $oQ (_ $o>Q quotable_inv g)).
      refine (qqiso_idr g $oQ (g $<oQ (IHf qfi)) $oQ _).
      refine (qqiso_assoc _ _ _).
    - refine (qqiso_fmap_id F v $oQ _).
      refine (qqiso_fmap (fmap F) (IHf qfi) $oQ _).
      refine ((qqiso_fmap_comp_opp F (quotable_inv f) f)).
  Defined.

  (** Finally, we can do the coinduction. *)
  CoFixpoint quotable_qiso {A : Type} `{IsCat1 A} {x y : A}
             (f : x $-> y) {qf : Quotable f} (qin : IsQQIso f)
    : IsQIso f.
  Proof.
    destruct (quotable_issect f) as [s qs qsi].
    destruct (quotable_isretr f) as [r qr qri].
    exact (Build_IsQIso _ _ _ _ _ _ (quotable_inv f) s r
                        (quotable_qiso _ _ _ _ _ _ _ s qs qsi) (quotable_qiso _ _ _ _ _ _ _ r qr qri)).
  Defined.

End QuoteQIso.

(** Now we can extract the statements we really want: quasi-isomorphisms and equivalences are closed under composition and functor action. *)

Global Instance isqiso_compose {A : Type} `{IsCat1 A} {a b c : A}
           (g : b $-> c) {gi : IsQIso g} (f : a $-> b) {fi : IsQIso f}
  : IsQIso (g $o f).
Proof.
  simple notypeclasses refine (QuoteQIso.quotable_qiso (g $o f) _); try exact _.
  - apply QuoteQIso.quote_comp; apply QuoteQIso.quote_unquote.
  - exact (gi,fi).
Defined.

Global Instance catie_compose {A : Type} `{IsCat1 A} {a b c : A}
           (g : b $-> c) {gi : CatIsEquiv g} (f : a $-> b) {fi : CatIsEquiv f}
  : CatIsEquiv (g $o f).
Proof.
  apply catie_isqiso, isqiso_compose; apply isqiso_catie; assumption.
Defined.

Definition cate_compose {A : Type} `{IsCat1 A} {a b c : A}
           (g : b $<~> c) (f : a $<~> b)
  : a $<~> c
  := Build_CatEquiv (g $o f).

Notation "g $oE f" := (cate_compose g f).

Global Instance transitive_cate {A} `{IsCat1 A}
  : Transitive (@CatEquiv A _ _ _)
  := fun a b c f g => cate_compose g f.

Global Instance isqiso_fmap {A B : Type} `{IsCat1 A} `{IsCat1 B}
           (F : A -> B) `{!IsFunctor0 F, !IsFunctor1 F}
           {a b : A} (f : a $-> b) {fi : IsQIso f}
  : IsQIso (fmap F f).
Proof.
  simple notypeclasses refine (QuoteQIso.quotable_qiso (fmap F f) _); try exact _.
  - refine (QuoteQIso.quote_fmap F f _); try exact _.
    apply QuoteQIso.quote_unquote.
  - exact fi.
Defined.

Global Instance catie_fmap {A B : Type} `{IsCat1 A} `{IsCat1 B}
           (F : A -> B) `{!IsFunctor0 F, !IsFunctor1 F}
           {a b : A} (f : a $-> b) {fi : CatIsEquiv f}
  : CatIsEquiv (fmap F f).
Proof.
  apply catie_isqiso, isqiso_fmap, isqiso_catie; assumption.
Defined.

Definition emap {A B : Type} `{IsCat1 A} `{IsCat1 B}
           (F : A -> B) `{!IsFunctor0 F, !IsFunctor1 F}
           {a b : A} (f : a $<~> b)
  : F a $<~> F b
  := Build_CatEquiv (fmap F f).

(** Hence equivalences are also closed under whiskering. *)
Definition cate_postwhisker {A} `{IsCat1 A} {a b c : A}
           {f g : a $-> b} (h : b $-> c) (p : f $<~> g)
  : h $o f $<~> h $o g
  := emap (cat_postcomp a h) p.

Notation "h $<oE p" := (cate_postwhisker h p) (at level 30).

Definition cate_prewhisker {A} `{IsCat1 A} {a b c : A}
           {f g : b $-> c} (p : f $<~> g) (h : a $-> b)
  : f $o h $<~> g $o h
  := emap (cat_precomp c h) p.

Notation "p $o>E h" := (cate_prewhisker p h) (at level 30).

(** We can also show that our redefined inverses are in fact inverses. *)
Definition cate_issect {A} `{IsCat1 A} {a b} (f : a $<~> b) 
  : f^-1$ $o f $<~> cat_id a.
Proof.
  simple refine (Build_CatEquiv (qiso_issect f) $oE _); try exact _.
  - rapply catie_isqiso.
  - apply cate_prewhisker, cate_buildequiv_fun.
Defined.

Definition cate_isretr {A} `{IsCat1 A} {a b} (f : a $<~> b)
  : f $o f^-1$ $<~> cat_id b.
Proof.
  simple refine (Build_CatEquiv (qiso_isretr f) $oE _); try exact _.
  - rapply catie_isqiso.
  - apply cate_postwhisker, cate_buildequiv_fun.
Defined.

(** We can also prove that 1-coherent functors compose.  *)
CoFixpoint isfunctor1_compose {A B C : Type} `{IsCat1 A} `{IsCat1 B} `{IsCat1 C}
           (G : B -> C) `{!IsFunctor0 G, !IsFunctor1 G}
           (F : A -> B) `{!IsFunctor0 F, !IsFunctor1 F}
  : IsFunctor1 (G o F).
Proof.
  unshelve econstructor.
  - intros a.
    refine (_ $oE emap (fmap G) (fmap_id F a)).
    exact (fmap_id G (F a)).
  - intros a b c f g.
    refine (_ $oE emap (fmap G) (fmap_comp F f g)).
    exact (fmap_comp G (fmap F f) (fmap F g)).
  - intros a b; cbn. 
    exact (isfunctor1_compose _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fmap G) _ _ (fmap F) _ _).
Defined.


(** ** Contractibility and universal properties *)

CoInductive CatContr (A : Type) `{IsGlob A} :=
{
  cat_center : A ;
  catcontr_hom : forall (a b : A), @CatContr (a $-> b) _ ;
}.

Existing Class CatContr.
Global Existing Instance catcontr_hom.

Class IsInitial {A : Type} `{IsGlob A} (a : A) :=
  catcontr_initial : forall b, CatContr (a $-> b).
Global Existing Instance catcontr_initial.

Class IsTerminal {A : Type} `{IsGlob A} (a : A) :=
  catcontr_terminal : forall b, CatContr (b $-> a).
Global Existing Instance catcontr_terminal.


(** ** (n,r)-categories *)

Inductive cat_dim : Type :=
| finite_cat_dim : nat -> cat_dim
| oo : cat_dim.

Coercion finite_cat_dim : nat >-> cat_dim.

Open Scope nat_scope.

Definition cat_dim_pred (n : cat_dim) : cat_dim
  := match n with
     | finite_cat_dim 0     => 0
     | finite_cat_dim (S n) => n
     | oo                   => oo
     end.

Notation "n .-1" := (cat_dim_pred n).

(** Quoting nLab, an (n,r)-category is an oo-category such that

- any j-morphism is an equivalence, for j>r.
- any two parallel j-morphisms are equivalent, for j>n.

We rephrase this coinductively by saying that

- if r=0, then any 1-morphism is an equivalence.
- if n=0, then any two parallel 1-morphisms are equivalent.
- every hom-category is an (n-1,r-1)-category.

If r > n+1, then an (n,r)-category is the same as an (n,n+1)-category, so usually we don't talk about such values of r, but at a technical level there is no need to exclude them. *)
CoInductive IsNRCat (n r : cat_dim) (A : Type) `{HasEquivs A} :=
{
  catie_isnrcat : (r = 0) -> forall (a b : A) (f : a $-> b), CatIsEquiv f ;
  cate_isnrcat : (n = 0) -> forall (a b : A) (f g : a $-> b), f $<~> g ;
  isnrcat_hom : forall (a b : A), @IsNRCat (n .-1) (r .-1) (a $-> b) _ _ _ ;
}.

Existing Class IsNRCat.
Global Existing Instances catie_isnrcat isnrcat_hom.
Arguments cate_isnrcat {n r A _ _ _ _} n0 {a b} f g.

(** An (oo-)groupoid is an (oo,0)-category. *)
Notation IsGpd0 A := (IsNRCat oo 0 A).

(** It follows that if n=0, then any inhabited hom-catgory is contractible. *)
CoFixpoint catcontr_isnrcat {n r A} `{IsNRCat n r A} (n0 : n = 0)
       {a b : A} (f : a $-> b)
  : CatContr (a $-> b).
Proof.
  unshelve econstructor.
  - assumption.
  - intros p q; refine (catcontr_isnrcat (n.-1) (r.-1) _ _ _ _ _ _ p q _).
    + symmetry in n0; destruct n0; reflexivity.
    + exact (cate_isnrcat n0 p q).
Defined.

Global Existing Instance catcontr_isnrcat.


(** ** Products *)

CoFixpoint isglob_prod {A B : Type} `{IsGlob A} `{IsGlob B}
  : IsGlob (A * B).
Proof.
  unshelve econstructor.
  - intros [a1 b1] [a2 b2]; exact ((a1 $-> a2) * (b1 $-> b2)).
  - intros [a1 b1] [a2 b2]. rapply isglob_prod.
Defined.

Global Existing Instance isglob_prod.

CoFixpoint isfunctor0_prod {A1 B1 A2 B2 : Type}
           `{IsGlob A1} `{IsGlob B1} `{IsGlob A2} `{IsGlob B2}
           (F1 : A1 -> B1) (F2 : A2 -> B2)
           `{!IsFunctor0 F1} `{!IsFunctor0 F2}
  : IsFunctor0 (fun z:A1*A2 => (F1 (fst z), F2 (snd z))).
Proof.
  simple notypeclasses refine (Build_IsFunctor0 _ _ _).
  - intros [a1 a2] [b1 b2] [f1 f2]; cbn.
    exact (fmap F1 f1 , fmap F2 f2).
  - intros; cbn; apply isfunctor0_prod; apply isfunctor0_fmap.
Defined.

CoFixpoint iscat0_prod {A B : Type} `{IsCat0 A} `{IsCat0 B}
  : IsCat0 (A * B).
Proof.
  unshelve econstructor.
  - intros [a1 b1] [a2 b2] [a3 b3] [f1 g1] [f2 g2].
    exact (f1 $o f2, g1 $o g2).
  - intros [a1 b1].
    exact (cat_id a1, cat_id b1).
  - intros [a1 b1] [a2 b2] [a3 b3] [h k]; cbn.
    apply isfunctor0_prod; apply isfunctor0_postcomp.
  - intros [a1 b1] [a2 b2] [a3 b3] [h k]; cbn.
    refine (isfunctor0_prod (fun g => g $o h) (fun g => g $o k)).
  - intros; rapply iscat0_prod.
Defined.

Global Existing Instance iscat0_prod.

CoFixpoint isfunctor0_pair {X A B : Type} `{IsGlob X} `{IsGlob A} `{IsGlob B}
           (F : X -> A) `{!IsFunctor0 F} (G : X -> B) `{!IsFunctor0 G}
  : IsFunctor0 (fun x => (F x, G x)).
Proof.
  simple notypeclasses refine (Build_IsFunctor0 _ _ _).
  - intros x y f; exact (fmap F f, fmap G f).
  - intros x y; refine (isfunctor0_pair _ _ _ _ _ _ (fmap F) _ (fmap G) _).
Defined.

Global Existing Instance isfunctor0_pair.

(** TODO: HasEquivs, 1-coherent categories *)


(** ** Laxity *)

(** Various things in higher category theory, such as comma categories and natural transformations, can be lax, colax, or pseudo separately at all levels.  In keeping with our coinductive approach, we define such an infinite list of notions of laxity as a coinductive stream.  *)

Inductive Laxity :=
| colax : Laxity
| pseudo : Laxity
| lax : Laxity.

CoInductive Stream (A : Type) := SCons
{
  head : A ;
  tail : Stream A
}.

Arguments SCons {A} _ _.
Arguments head {A} _.
Arguments tail {A} _.
Notation oplax := colax (only parsing).

CoFixpoint all_pseudo : Stream Laxity := SCons pseudo all_pseudo.
Definition one_lax : Stream Laxity := SCons lax all_pseudo.
Definition one_colax : Stream Laxity := SCons colax all_pseudo.

(** It may seem backwards for [colax] to mean a morphism "forwards" and [lax] a morphism "backwards", but that's what matches the standard terminology for natural transformations. *)
Definition lHom (l : Laxity) {A : Type} `{HasEquivs A} (a b : A) :=
  match l with
  | colax => (a $-> b)
  | pseudo => (a $<~> b)
  | lax => (b $-> a)
  end.

Definition lcat_id (l : Laxity) {A : Type} `{IsCat1 A} (a : A)
  : lHom l a a
  := match l return lHom l a a with
  | colax => cat_id a
  | pseudo => cate_id a
  | lax => cat_id a
  end.


(** ** Comma categories *)

(** We define the comma category of [F : A -> C] and [G : B -> C] as a displayed category over [A * B], of which we can then take the sigma-type (but also other things like the pi-type, or pullbacks along functors). *)

Definition GenDComma (l : Stream Laxity)
           {A B C : Type} `{IsGlob A} `{IsGlob B} `{HasEquivs C}
           (F : A -> C) `{!IsFunctor0 F} (G : B -> C) `{!IsFunctor0 G}
           (z : A * B)
  := lHom (head l) (F (fst z)) (G (snd z)).

Notation DIsoComma := (GenDComma all_pseudo).
Notation DComma := (GenDComma one_colax).

(** This is one of the sneakiest coinductions so far: we have to identify the hom-categories of a comma category as comma categories themselves.  Given objects [p1 : F a1 $-> G b1] and [p2 : F a2 $-> G b2] of the comma (F/G), a morphism [p1 $-> p2] consists of morphisms [f : a1 $-> a2] and [g : b1 $-> b2] together with a morphism (perhaps invertible) [(p2 $o fmap F f) $-> (fmap G g $o p1)].  But this is an *object* of the comma category between the composite functors

(a1 $-> a2)  --(fmap F)-->  (F a1 $-> F a2)  --(p2 $o ?)-->  (F a1 $-> G b2)
(b1 $-> b2)  --(fmap G)-->  (G b1 $-> G b2)  --(? $o p1)-->  (F a1 $-> G b2).
*)
CoFixpoint isdglob_gendcomma (l : Stream Laxity)
           {A B C : Type} `{IsGlob A} `{IsGlob B} `{HasEquivs C}
           (F : A -> C) `{!IsFunctor0 F} (G : B -> C) `{!IsFunctor0 G}
  : IsDGlob (GenDComma l F G).
Proof.
  unshelve econstructor.
  - intros [a1 b1] [a2 b2] fg p1 p2; unfold GenDComma in *; cbn in *.
    destruct (head l); cbn in *.
    (** The colax and pseudo cases are the same, with an equivalence just regarded as a map. *)
    1-2:refine (GenDComma (tail l) (cat_postcomp (F a1) p2 o fmap F) (cat_precomp (G b2) p1 o fmap G) fg).
    refine (GenDComma (tail l) (cat_precomp (F a2) p1 o fmap F) (cat_postcomp (G b1) p2 o fmap G) fg).
  - intros [a1 b1] [a2 b2] p1 p2; unfold GenDComma in p1, p2.
    destruct (head l); cbn; apply isdglob_gendcomma.
Defined.

Global Existing Instance isdglob_gendcomma.

(** The standard comma category is the sigma-category of the displayed one. *)
Definition GenComma (l : Stream Laxity)
           {A B C : Type} `{IsGlob A} `{IsGlob B} `{HasEquivs C}
           (F : A -> C) `{!IsFunctor0 F} (G : B -> C) `{!IsFunctor0 G}
  := sig (GenDComma l F G).

Notation IsoComma := (GenComma all_pseudo).
Notation Comma := (GenComma one_colax).

(** The arrow category of [A] is the comma category of its identity functor over itself. *)
Definition GenDArrow (l : Stream Laxity) (A : Type) `{HasEquivs A}
  := @GenDComma l A A A _ _ _ _ _ idmap _ idmap _.

(** Note that the general comma category [GenDComma l F G] could be obtained by pullback of [GenDArrow l C] along [F*G : A*B -> C*C].  However, a coinductive definition of [GenDArrow] would involve more general comma categories at the coinductive step, so it makes more sense (and probably makes it easier to satisfy Coq's guardedness checker) to define general comma categories directly. *)

(** TODO: If [A] and [B] are 0-coherent and [F] and [G] are 1-coherent, then the comma category should be 1-coherent with equivalences, and so on. *)


(** ** Inserters *)

(** The inserter of [F,G : A -> B] is the pullback of their comma category along the diagonal [A -> A*A].  Like a comma category it comes in both displayed and total versions; note that having the displayed version of the comma category is what allows us to take this pullback strictly.  *)

Definition GenDInserter (l : Stream Laxity)
           {A B : Type} `{IsGlob A} `{HasEquivs B}
           (F G : A -> B) `{!IsFunctor0 F, !IsFunctor0 G}
           (a : A)
  := GenDComma l F G (a,a).

Notation DIsoInserter := (GenDInserter all_pseudo).
Notation DInserter := (GenDComma one_colax).

Global Instance isdglob_gendinserter (l : Stream Laxity)
       {A B : Type} `{IsGlob A} `{HasEquivs B}
       (F G : A -> B) `{!IsFunctor0 F, !IsFunctor0 G}
  : IsDGlob (GenDInserter l F G)
  := isdglob_compose (GenDComma l F G) (fun a => (a,a)).

Definition GenInserter (l : Stream Laxity)
           {A B : Type} `{IsGlob A} `{HasEquivs B}
           (F G : A -> B) `{!IsFunctor0 F, !IsFunctor0 G}
  := sig (GenDInserter l F G).

Notation IsoInserter := (GenInserter all_pseudo).
Notation Inserter := (GenComma one_colax).

(** For instance, the category of prespectra (resp. spectra) should be the inserter (resp. isoinserter) of the identity functor of (nat -> pType) over a functor [shift o loops]. *)


(** ** 1-natural transformations *)

(** A natural transformation [F $=> G] is a section of their displayed inserter.  The freedom to choose laxities at all dimensions carries over, although we insist that a transformation always goes from [F] to [G] so that the inserter is colax at the bottom level. *)

Definition Transformation {A B : Type} `{IsGlob B} (F : A -> B) (G : A -> B)
  := forall (a : A), F a $-> G a.

Notation "F $=> G" := (Transformation F G).

Class IsGenNatural1 (l : Stream Laxity)
      {A B : Type} `{IsGlob A} `{HasEquivs B}
      (F G : A -> B) `{!IsFunctor0 F, !IsFunctor0 G}
      (alpha : F $=> G)
  := iscatsect0_isgennatural1 : IsCatSect0 (B := GenDInserter (SCons colax l) F G) alpha.

Global Existing Instance iscatsect0_isgennatural1.

Definition isgennat (l : Stream Laxity) {A B : Type} `{IsGlob A} `{HasEquivs B}
      {F : A -> B} `{!IsFunctor0 F} {G : A -> B} `{!IsFunctor0 G}
      (alpha : F $=> G) {alnat : IsGenNatural1 l F G alpha}
      {x y : A} (f : x $-> y)
  : lHom (head l) (alpha y $o fmap F f) (fmap G f $o alpha x)
  := fmapD (B := GenDInserter (SCons colax l) F G) alpha f.

Notation IsNatural1 := (IsGenNatural1 all_pseudo).

Definition isnat {A B : Type} `{IsGlob A} `{HasEquivs B}
      {F : A -> B} `{!IsFunctor0 F} {G : A -> B} `{!IsFunctor0 G}
      (alpha : F $=> G) {alnat : IsNatural1 F G alpha}
      {x y : A} (f : x $-> y)
  : (alpha y $o fmap F f) $<~> (fmap G f $o alpha x)
  := isgennat all_pseudo alpha f.

(** If we generalized comma categories (and hence inserters) to act on category-sections rather than just functors, we could in principle iterate this approach to define modifications and higher transfors, analogously to how we iterate [isglob_forall] to define all the higher structure of [Type] and similarly for [pType].  However, since the level of coherence seems to go down by one each time we apply a comma construction, we probably wouldn't be able to use this to define a whole oo-category of oo-categories at any fixed coherence level.  *)

(* TODO: Examples *)


(** ** Monoidal oo-categories *)

(** With the coinductive setup, it seems at least *more* plausibly sensible to define monoidal categories via delooping.  The definition could look something like this: *)

Definition isglob_deloop (A : Type) `{IsGlob A}
  : IsGlob Unit
  := (Build_IsGlob Unit (fun _ _ => A) (fun _ _ => _)).

Class IsMonCat0 (A : Type) `{IsGlob A} :=
{
  iscat0_deloop : @IsCat0 Unit (isglob_deloop A)
}.

Arguments iscat0_deloop A {_ _}.

(** NB: [isglob_deloop] and [iscat0_deloop] are *not* [Instance]s!  But the following is: *)

Global Instance iscat0_ismoncat0 {A : Type} `{IsMonCat0 A}
  : IsCat0 A
  := @iscat0_hom _ _ (iscat0_deloop A) tt tt.

Definition moncat_tens {A : Type} `{IsMonCat0 A}
  : A -> A -> A
  := @cat_comp _ _ (iscat0_deloop A) tt tt tt.

Notation "a [x] b" := (moncat_tens a b) (at level 30).

Definition moncat_unit {A : Type} `{IsMonCat0 A}
  : A
  := @cat_id _ _ (iscat0_deloop A) tt.

(** I'm still not entirely convinced this is the best way to go.  One obvious potential drawback is that [iscat0_ismoncat0] is not a parameter, so we can't say "[A] with this specified category structure has a monoidal structure".  But it would almost certainly reduce code duplication, especially if we end up needing higher-coherent monoidal (oo-)categories. *)


(** ** 2-coherent oo-functors *)

(* For some strange reason calling this [IsFunctor2] doesn't work!  A parsing bug? *)
CoInductive IsFunctorTwo {A B : Type} `{IsCat1 A} `{IsCat1 B}
            (F : A -> B) `{!IsFunctor0 F, !IsFunctor1 F} : Type :=
{
  (* fmap_comp is 1-natural -- in each variable separately, I suppose *)
  (* pseudofunctor axioms for fmap_id and fmap_comp, up to equivalences. *)
  isfunctor2_fmap : forall (a b : A),
      (@IsFunctorTwo (a $-> b) (F a $-> F b) _ _ _ _ _ _ _ _ (@fmap _ _ _ _ F _ a b) _ _);
}.

Existing Class IsFunctorTwo.
Global Existing Instance isfunctor2_fmap.

(* TODO: Examples *)


(** ** 2-coherent oo-categories *)

CoInductive IsCat2 (A : Type) `{IsCat1 A} : Type :=
{
  (* associator and unitors are 1-natural in all variables separately *)
  (* pentagon and triangle axioms hold *)
  (* pre- and post-composition are 2-coherent functors *)
  (* axioms on Gray interchange for associativity and 1-functoriality *)
  iscat2_hom : forall (x y : A), @IsCat2 (x $-> y) _ _ _ _ ;
}.

Existing Class IsCat2.
Global Existing Instance iscat2_hom.

(* TODO: Examples *)

Require Import Basics WildCat.Core WildCat.Type WildCat.Forall WildCat.UnitCat WildCat.Paths.

Global Instance is1cat_strong_unit : Is1Cat_Strong Unit.
Proof.
  snrapply Build_Is1Cat_Strong.
  1,2,3:exact _.
  all:repeat progress intros []; cbn.
  1-2:econstructor; repeat progress intros []; cbn; exact tt.
  all:reflexivity.
Defined.

Section AssumeFunext.
Context `{Funext}.

Unset Primitive Projections.

Record SigOf {S : Type} `{Is1Cat_Strong S} :=
{
  bot : Type@{i} ;
  deriv : (bot -> Type@{i}) -> S ;
  is0functor_deriv : Is0Functor deriv ;
}.
Arguments SigOf S {_ _ _}.

Record Cat1_Strong :=
{
  cat1_carrier : Type ;
  isgraph_cat1 : IsGraph cat1_carrier ;
  is01cat_cat1 : Is01Cat cat1_carrier ;
  is1cat_cat1 : Is1Cat_Strong cat1_carrier ;
}.

Fixpoint Sig (n : nat) : Cat1_Strong.
Proof.
  destruct n; snrefine (Build_Cat1_Strong _ _ _ _).
  1: exact Unit.
  1-3: exact _.
  1:exact (@SigOf (cat1_carrier (Sig n)) (isgraph_cat1 (Sig n)) (is01cat_cat1 (Sig n)) (is1cat_cat1 (Sig n))).
  all:pose (isgraph_cat1 (Sig n)); pose (is01cat_cat1 (Sig n)); pose (is1cat_cat1 (Sig n)).
  - constructor; intros LL MM.
    refine { abot : LL.(bot) -> MM.(bot) & _ }.
    exact (forall M : MM.(bot) -> Type, LL.(deriv) (M o abot) $-> MM.(deriv) M). 
  - constructor.
    + intros LL; cbn.
      exists idmap.
      intros M; apply Id.
    + intros LL MM NN [bbot b'] [abot a']; cbn.
      exists (bbot o abot).
      intros N; refine (b' N $o _).
      exact (a' (N o bbot)).
  - snrapply Build_Is1Cat_Strong; intros;
    [ apply isgraph_paths
    | apply is01cat_paths
    | apply is0gpd_paths
    | constructor; intros ? ? p; destruct p; reflexivity
    | constructor; intros ? ? p; destruct p; reflexivity
    | | | ]; apply (ap (exist _ _)), path_forall; intros M;
    [ apply cat_assoc_strong | apply cat_idl_strong | apply cat_idr_strong ].
Defined.

Typeclasses Opaque cat1_carrier is01cat_cat1 is1cat_cat1 bot deriv is0functor_deriv Hom.

Global Instance isgraph_sig n : IsGraph (cat1_carrier (Sig n))
  := isgraph_cat1 (Sig n).

Goal forall (x y:cat1_carrier (Sig 0)) (f : x $-> y), Funext.
  intros x y f.
  (** I want to destruct f.  This should be easy: *)
  change Unit in f; destruct f.
  Undo.
  (** But Coq can't manage to simplify [f] before destructing it: *)
  destruct f. (* Hangs *)
  Undo.
  cbn in f. (* Hangs *)
  Undo.
  (** What seems to be sufficient to make it work is a couple of manual unfoldings: *)
  unfold isgraph_sig in f.  
  unfold Sig in f.
  cbn in f.
Qed.

End AssumeFunext.

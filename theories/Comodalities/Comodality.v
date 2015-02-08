(* -*- mode: coq; mode: visual-line -*- *)
Require Import HoTT.Basics.Overture HoTT.Basics.Equivalences.
Require Import HoTT.Types.Bool HoTT.Types.Prod.
Require Import HoTT.HProp.

Local Open Scope path_scope.

(** TODO: Find another word than "closed"; that has confusing topological connotations. *)

(** * Comodalities *)

(** ** About parametrized module types

We use parametrized module types.  Since the documentation on modules is poor, we include a brief introduction to parametrized module types.  A parametrized module

<<
Module foo (X : Bar) : Foo.
  ...
End foo.
>>

is a *function* from [Bar]s to [Foo]s, the module version of [(fun X => ...) : Bar -> Foo].  A parametrized module *type*, on the other hand

<<
Module Type Foo (X : Bar).
  ...
End Foo.
>>

is a "dependent module type", i.e. a function from [Bar]s to module-types.  Thus, if we apply it to an argument, we obtain an ordinary module type that can then be implemented:

<<
Module bar : Bar.
  ...
End bar.

Module foo <: Foo bar.
  ...
End foo.
>>

A dependent module type also gives rise to a "universally quantified module type", a sort of module version of [(forall x:Bar, Foo x)].  We can implement this, essentially defining a "dependently type module function", as follows:

<<
Module allfoo (X : Bar) <: Foo X.
  ...
End allfoo.
>>

We can also hypothesize a dependently typed module function, but confusingly the [forall] operation on modules is silent: the way to say [(forall x:Bar, Foo x)] in a hypothesis is to just say [Foo], unapplied.  Thus, we could say

<<
Module Baz (foo : Foo).
  Module bar <: Bar.
    ...
  End bar.
  Module foobar := foo bar.
  ...
End Baz.
>>

(Given this, you might think that an alternative way to define [allfoo] would begin [Module allfoo <: Foo.].  Coq does accept such a beginning to a module declaration, but unfortunately there doesn't seem to be a way to complete it.)


*** Applications of module functions

Modules and module functions require rather more boilerplate code than ordinary records and functions.  One reason for this is that all applications of module functions must be named before they can be used.  For instance, if we have

<<
Module Type Foo.
  ...
End Foo.

Module bar (f : Foo).
  Definition baz := ...
End bar.

Module foo <: Foo.
  ...
End foo.
>>

then we may want to apply [bar] to [foo] and then extract its field [baz], which we would naturally think of writing [(bar foo).baz].  Unfortunately, Coq does not accept this; it requires us to first give [bar foo] a name.  That is, we have to write

<<
Module bar_foo := bar foo.
>>

and then talk about [bar_foo.baz].

Roughly the same rule affects parameters of dependently typed module functions.  For instance, suppose we have

<<
Module Type Foo.
  ...
End Foo.

Module Type Bar (f : Foo).
  ...
End Bar.

Module endofoo (f : Foo) <: Foo.
  ...
End endofoo.
>>

In other words, we have a module type [Foo], a dependent module type [Bar], and a module endomorphism [endofoo] mapping [Foo]s to [Foo]s.  Now suppose we want to define another module type that takes as parameters a module [f : Foo] and also a module [b : Bar (endofoo f)].  We might naively think first that we could write

<<
Module baz (f : Foo) (b : Bar (endofoo f)).
>>

but this is also rejected, with the somewhat cryptic error message "Application of modules is restricted to paths".  The meaning is that we can't talk about [endofoo f] without giving it its own name.  Thus, in order to define our dependently typed module function [baz], we have to actually nest two modules, as follows:

<<
Module baz_outer (f : Foo).
  Module endofoo_f := endofoo f.
  Module baz_inner (b : Bar endofoo_f).
    ..
  End baz_inner.
End baz_outer.
>>

When applying this function to a particular instance [f0 : Foo] and [b0 : Bar (endofoo f0)], we have to likewise do it in two stages:

<<
Module baz_outer_f0 := baz_outer f0.
Module baz_inner_f0 := baz_outer_f0.baz_inner b0.
>>

This looks mainly like extra boilerplate, but it is complicated further by the next point.


*** Module functions are productive

Another source of pitfalls is the fact that module functions are *productive* rather than *applicative*.  What this means is that whenever we apply a module (type) function to arguments, it produces *new names* and (sometimes) new objects, *even if the application is word-for-word the same as one that previously appeared*.  For example, if we write

<<
Module Type Foo.
  Parameter f : Type1.
End Foo.

Module myfoo : Foo.
  Definition f := Unit.
End myfoo.

Module Bar (foo : Foo).
  Definition b := foo.f.
End Bar.

Module mybar1 := Bar myfoo.
Module mybar2 := Bar myfoo.
>>

then [mybar1.b] and [mybar2.b] are syntactically different objects.  In the above example, there is not a huge problem because these syntactically different objects happen to be *definitionally* equal, and thus we can still write something like

<<
Definition frob : mybar1.b -> mybar2.b := idmap.
>>

(It can sometimes cause problems with typeclass inference, though.)  However, it becomes more serious if the field [b] is not given by a *definition* but rather a postulate or parameter, such as if instead of [Bar] above we define

<<
Module Type Baz (foo : Foo).
  Parameter b : Type.
End Baz.

Declare Module mybaz := Baz.

Module mybaz1 := mybaz myfoo.
Module mybaz2 := mybaz myfoo.
>>

(The command [Declare Module] is like [Parameter], but for modules and module types rather than ordinary terms and types.)  In this case [mybaz1.b] and [mybaz2.b] are *actually* different, because they are syntactically different and they have no underlying definition to give any other way of regarding them as the same.  Thus, 

<<
Definition frob : mybaz1.b -> mybaz2.b := idmap.
>>

will fail.  We include some remarks later on about how we work around this problem.  There is another related problem called bug 4003 (https://coq.inria.fr/bugs/show_bug.cgi?id=4003), which we will have to work around in some places. *)

(** ** Module wrappers *)

(** We begin by defining some module types that wrap ordinary types, functions, and statements about them, turning them from internal statements about inhabitants of the universe to external statements about closed types.  In general, we adopt the convention that a suffix of [M] means a module or module type wrapper, which has a field [m] that indicates the actual object under consideration.  Of course, no such module should be [Import]ed; the [m] fields should always be used dot-qualified.  *)

(** An instantiation of [TypeM] is a closed type, i.e. a type in the empty context. *)
Module Type TypeM.
  (** Unfortunately, due to the way polymorphic module types work, a parameter [m : Type] can only be instantiated by a closed type that lives in _every_ universe.  In particular, we wouldn't be able to instantiate it by [Type].  We sort-of work around this by declaring [m] to have type [Type2]; this enables us to instantiate it by [Type] once, as long as we don't demand that that [Type] also contain some smaller universe.  It seems unlikely that we would need that, but if we ever do, we could always come back here and change [Type2] to [Type3]. *)
  Parameter m : Type2.
End TypeM.

(** For example, we have the unit type. *)
Module UnitM <: TypeM.
  (** We have to give the [: Type2] annotation for it to be sufficiently polymorphic. *)
  Definition m : Type2@{j i} := Unit@{j}.
End UnitM.

(** And the empty type, etc. etc. *)
Module EmptyM <: TypeM.
  Definition m : Type2@{j i} := Empty@{j}.
End EmptyM.

Module BoolM <: TypeM.
  Definition m : Type2@{j i} := Bool@{j}.
End BoolM.

Module NatM <: TypeM.
  Definition m : Type2@{j i} := nat.
End NatM.

(** And, as promised, the smallest (non-[Set]) universe. *)
Module Type1M <: TypeM.
  (** Confusingly, although the universe annotation on [Unit] and [Empty] specifies the universe *in* which they live, the universe annotation on [Type1] specifies the universe that it *is*, which must be smaller than the one in which it lives. *)
  Definition m : Type2@{j i} := Type1@{i}.
End Type1M.

(** Operations on types are wrapped by module functions. *)
Module SumM (XM : TypeM) (YM : TypeM) <: TypeM.
  Definition m := XM.m + YM.m.
End SumM.

Module ProdM (XM : TypeM) (YM : TypeM) <: TypeM.
  Definition m := XM.m * YM.m.
End ProdM.

(** Similarly, an instantiation of [FunctionM XM YM] is a function [XM.m -> YM.m] in the empty context. *)
Module Type FunctionM (XM YM : TypeM).
  Parameter m : XM.m -> YM.m.
End FunctionM.

(** For example, we have the identity function. *)
Module IdmapM (XM : TypeM) <: FunctionM XM XM.
  Definition m := idmap : XM.m -> XM.m.
End IdmapM.

(** And likewise for closed homotopies. *)
Module Type HomotopyM (XM YM : TypeM) (fM gM : FunctionM XM YM).
  Parameter m : fM.m == gM.m.
End HomotopyM.

(** And equivalences. *)
Module Type IsEquivM (XM YM : TypeM) (fM : FunctionM XM YM).
  Parameter m : IsEquiv fM.m.
End IsEquivM.

Module Type EquivM (XM YM : TypeM) <: FunctionM XM YM.
  Parameter m : XM.m -> YM.m.
  Parameter m_isequiv : IsEquiv m.
End EquivM.
(** Note that the field [m] of [EquivM XM YM] means that it could also be an instantiation of the module type [FunctionM XM YM].  Since modules are duck-typed, that means we can use an [EquivM XM YM] wherever a [FunctionM XM YM] is expected; this is sort of a module version of the fact that [equiv_fun] is a [Coercion].  The declaration [<: FunctionM XM YM] at the declaration of [EquivM] instructs Coq to verify that this duck-typing is possible. *)

(** And sections *)
Module Type SectM (XM YM : TypeM) (sM : FunctionM XM YM) (rM : FunctionM YM XM).
  Parameter m : Sect sM.m rM.m.
End SectM.

(** And truncation *)
Module Type IsHPropM (XM : TypeM).
  Parameter m : IsHProp XM.m.
End IsHPropM.

(** Composition of closed functions. *)
Module ComposeM (XM YM ZM : TypeM)
       (gM : FunctionM YM ZM) (fM : FunctionM XM YM)
    <: FunctionM XM ZM.
  Definition m := gM.m o fM.m.
End ComposeM.

(** And postcomposition of a closed homotopy by a closed function.  At one point I thought we would need this, but we don't actually seem to. *)
Module ApM (XM YM ZM : TypeM)
       (hM : FunctionM YM ZM) (fM gM : FunctionM XM YM)
       (pM : HomotopyM XM YM fM gM).
  Module hfM := ComposeM XM YM ZM hM fM.
  Module hgM := ComposeM XM YM ZM hM gM.
  Module hpM <: HomotopyM XM ZM hfM hgM.
    Definition m x := ap hM.m (pM.m x).
  End hpM.
End ApM.

(** ** Subuniverses *)

(** The next definition is a bit confusing: [Subuniverse] is the dependent module-type [fun (_:TypeM) => hProp].  Thus, an instantiation of [Subuniverse XM] is just a single (closed) [hProp].  However, generally what will want is instead to instantiate the corresponding dependent module-function type [forall (X:TypeM), Subuniverse M], i.e. the module version of [TypeM -> hProp].  As discussed above, this is hypothesized with [F : Subuniverse]; thus it is an operation taking each closed type [X : TypeM] to a closed [hProp] representing the predicate that [X] lies in the subuniverse.  This closed [hProp] is morally [(F X).m], although in practice we have to access it by declaring [Module FXM := F X.] and then calling [FXM.m].

Ideally, we would like this to be an *external* predicate on closed types rather than an operation assigning an internal predicate to each of them, but there doesn't seem to be any way to do that.  Fortunately, for comodalities we can always internalize the "in the subuniverse" predicate to be [IsEquiv fromF]. *)
Module Type Subuniverse
       (** We indicate the fact that a parameter of a parametrized module type is generally universally quantified over by adding a [forall] comment before it. *)
       (** forall *)
       (XM : TypeM).
  Parameter m : Type2.
  (** As with modalities, we allow a [Funext] hypothesis in the proof that this is an hprop. *)
  Parameter m_ishprop : Funext -> IsHProp m.
End Subuniverse.

(** However if we are given a closed type, we can assert that it is "closedly" in the subuniverse. *)
Module Type InM (InF : Subuniverse) (XM : TypeM).
  Module InF_M := InF XM.
  Parameter m : InF_M.m.
End InM.
(** The rule that all modules must be defined at top level means we need names for more things than one might expect.  Specifically, for modules [InF : Subuniverse] and [XM : TypeM], we have the following:

1. The module [InF XM], which a module wrapper whose field [m] is an hprop that is an *assertion* that [X] lies in the subuniverse [F].  When we need a name for this module (which we do whenever we want to extract its field), we will call it [InF_XM].

2. The module type [InM InF XM], which is a module *type* wrapper whose implementations are witnesses, in the empty context, that [X] lies in [F].  We don't usually need a special name for this module type.

3. A proven or assumed implementation of [InM InF XM], which is a module wrapper around a closed witness that [X] lies in [F].  When we need a name for such a module, we will call it [isinF_XM]. *)

(** We are particularly interested in subuniverses that are closed under various operations, generally finite limits. *)

Module Type InF_Unit_M (InF : Subuniverse) <: InM InF UnitM.
  Module InF_M := InF UnitM.
  Parameter m : InF_M.m.
  (** An instantiation of this module type can be duck-typed as [InM InF UnitM].  In fact there is not much point to declaring this module type, since we could always write [InM InF UnitM] instead; we do it for parallelism with the other examples of this sort. *)
End InF_Unit_M.

Module Type InF_Prod_M (InF : Subuniverse)
       (** forall *)
       (XM YM : TypeM)
       (isinF_XM : InM InF XM) (isinF_YM : InM InF YM).
  Module PM := ProdM XM YM.
  Module InF_M := InF PM.
  Parameter m : InF_M.m.
  (** An instantiation of this module type can be duck-typed as [InM InF PM].  Note that we cannot ask Coq to verify this with [<: InM InF PM], since [PM] is only declared *inside* the module; this doesn't prevent the the duck-typing however. *)
End InF_Prod_M.

(** We could also do pullbacks, etc., if we have a use for them. *)

(** ** Corecursion principles *)

(** Next we have to express the universal property; we need a way to say that postcomposition with a map is an equivalence.  You might think naively that we could assert a closed proof that postcomposition with [from F] is an equivalence.  However, this would be too strong, as it would assert an external equivalence of *internal* hom-objects.  (Even with all the care we have exercised so far, a slip-up here would still be enough to reproduce the no-go result of [CoreflectiveSubuniverse].)  Instead, we want an equivalence of *external* hom-objects, which in particular means that we can only induce a function [X -> F Y] from a *closed* function [X -> Y].

Thus, we need to wrap each *part* of a definition of [IsEquiv] in modules, rather than the whole thing in one module.  We will use a "liftable" style for this, dual to the notion of [ExtendableAlong] that we used for reflective subuniverses.  As above, all the liftings have to act only on closed types and functions, because the universal property is not internalizable.  Unfortunately, this means that we cannot describe an "[oo]" sort of liftability analogous to [ooExtendableAlong], since we can't define a module type by [nat]-recursion.

We can, of course, state [n]-liftability for any finite fixed external natural number [n].  Unfortunately, however, none of these is actually enough to ensure that postcomposition is actually an external equivalence!  The problem is that module functions act on closed *terms* and not on the "external oo-groupoid of functions", which we don't have any way to talk about anyway.  Thus, 1-liftability actually asserts only that postcomposition is a (-1)-connected map (i.e. essentially surjective), 2-liftability asserts that it is 0-connected (essentially surjective on objects and 1-morphisms), and so on.  Assuming [Funext] won't help since there isn't even any way to [ap] a module function.

This means that our definition will necessarily be incomplete; we have to choose some external finite [n] to assert [n]-liftability, whereas we would really like to have it for all [n].  However, if it turns out that we need a greater value of [n], we can always come back to this file and increase it; since implementations of [Comodality] are almost always hypothesized rather than constructed, this won't break very much (if anything).

For now, we stick with [n=2], which is enough for everything we've needed so far.

Note also that the hypothesis that [XM.m] lies in [F] is again internal rather than external.  This is again obtainable from an internal definition as [IsEquiv fromF].

We will generally apply these modules to four arguments, namely the subuniverse, a type, its coreflection, and the counit map, and then assert them universally quantified over the remaining data, giving the universal property of the counit.  To indicate this, we add the comment [forall] in between the first four arguments and the remaining ones. *)
Module Type CorecM (InF : Subuniverse)
       (YM ZM : TypeM) (fM : FunctionM YM ZM)
       (** forall *)
       (XM : TypeM) (isinF_XM : InM InF XM)
       (gM : FunctionM XM ZM).
  Parameter m : XM.m -> YM.m.
  (** This wrapper module contains two data, of which one is the lift and the other its computation law.  Rather than force ourselves to define two separate wrappers, we denote the latter one by [m_beta]. *)
  Parameter m_beta : fM.m o m == gM.m.
End CorecM.
(** Note that, like [EquivM], an implementation of [CorecM] satisfies the interface of a [FunctionM XM YM], and thus (since modules are duck-typed) it can be used as one. *)

Module Type CoindpathsM (F : Subuniverse)
       (YM ZM : TypeM) (fM : FunctionM YM ZM)
       (** forall *)
       (XM : TypeM) (isinF_XM : InM F XM)
       (hM kM : FunctionM XM YM).
  (** All intermediate modules have to be given names, so in order to hypothesize a closed homotopy from [f o h] to [f o k], we have to give names to those [FunctionM]s. *)
  Module domM := ComposeM XM YM ZM fM hM.
  Module codM := ComposeM XM YM ZM fM kM.
  (** The module name [mM] means that this module is the "content" of the wrapper [CoindpathsM], but that it itself has to be a module because it needs to take an extra module parameter. *)
  Declare Module mM (pM : HomotopyM XM ZM domM codM)
    : HomotopyM XM YM hM kM.
  (** Again, we include the computation law in the same module wrapper. *)
  Module m_betaM (pM : HomotopyM XM ZM domM codM).
    Module liftM := mM pM.
    Parameter m : forall x:XM.m, ap fM.m (liftM.m x) = pM.m x.
  End m_betaM.
End CoindpathsM.

(** ** Comodalities *)

(** Finally we are ready to define a comodality, by which we mean a subuniverse with coreflections.  Again we are thinking of this as usually partially applied; given [InF : Subuniverse], an instantiation of [Comodality InF] is an operation taking each closed type [XM : TypeM] to another closed type [m] that lies [InF], together with a closed function [from] from [m] to [XM.m], such that for any other closed type, if it lies in the subuniverse then maps out of it are liftable along [from]. *)
Module Type Comodality (InF : Subuniverse)
       (** forall *)
       (XM : TypeM).
  (** We could have included [InF] as part of the data of [Comodality].  We instead make it a parameter, because in some cases we want to be able to specify what it is.  For instance, it might be a wrapper around [In O] for some (monadic) modality [O]. *)

  (** The coreflection of [X].  Since (as for reflective subuniverses and modalities) we use the name of the subuniverse as also the coreflector operation on types, we call this [m] as the "content" of the wrapper. *)
  Parameter m : Type2.
  (** We wrap this type in a module as well.  Note, however, that since we've named the type [m], an instantiation [FXM : Comodality InF XM] itself satisfies the interface of a [TypeM], and hence by duck-typing can be used as one.  Thus, if [FXM : Comodality InF XM], instead of [FXM.mM] we can often write just [FXM]. *)
  Module mM <: TypeM.
    Definition m := m.
  End mM.

  (** The coreflection lies in the subuniverse. *)
  Declare Module isinF_mM : InM InF mM.

  (** The coreflection counit map from [FX] to [X] *)
  Parameter from : m -> XM.m.
  Module fromM <: FunctionM mM XM.
    Definition m := from.
  End fromM.

  (** The universal property *)
  Declare Module corecM : CorecM InF mM XM fromM.
  Declare Module coindpathsM : CoindpathsM InF mM XM fromM.

  (** Finally, we assert repleteness.  For technical reasons, it is easier to assert this in the following form: any type equivalent to [F X] lies in [F].  We will be able to show that if [X] lies in [F], then [from F X] is an equivalence; thus any type equivalent to a type in [F] will also be equivalent to one of the form [F X] and this can be applied. *)
  Declare Module repleteM (YM : TypeM) (EM : EquivM mM YM) : InM InF YM.

End Comodality.

(** If we hypothesize a comodality [F : Comodality InF] (as we will shortly do), then for any wrapped type [XM : TypeM], the application [F XM] is a module containing all the data about the coreflection of [XM] into [F].  We generally name it something like [FXM] (since we have to name it before doing anything else with it).

However, because module functions are productive, if in two different places we construct [F XM] for the same [F] and [XM], the resulting modules [FXM] will be different, and in particular the coreflected types [FXM.m] they produce will not be convertible.  This can be a serious problem, so we generally avoid actually applying [F] unless we know that the particular coreflected type it produces will be irrelevant outside some current module or development (e.g. in proving that [Empty] lies in [F], we need to use [F Empty], but the end conclusion doesn't refer to it).

Instead, for every hypothesized [XM : TypeM] to which we will need to apply [F], we additionally *hypothesize* an inhabitant [FXM : Comodality InF XM].  This way whenever our module-lemma gets used elsewhere, we can pass around these inhabitants rather than actually applying [F] and producing new names.  Tthis is extra convenient because by duck-typing, we have [FXM : TypeM] as well.

From a category-theoretic perspective, this is actually quite natural: an inhabitant of [Comodality InF XM] is *a* coreflection of [XM], and we are saying that rather than use a particular specified *operation* sending every type to a specified coreflection, we work instead with *any* coreflection at all of the particular types in question.  That is, we are taking a "nonalgebraic" approach to coreflections. *)

Module Comodality_Theory (InF : Subuniverse) (F : Comodality InF).

  (** ** Recognizing comodal types with retractions *)

  (** If [from F X] admits a section, then [X] lies in [F].  As mentioned above, we state this as a module-theorem about *any* coreflection of [X].  This turns out to have as an additional benefit that it removes a level of module indirection; otherwise we would have to define [inF_from_F_section_M] to take only the parameter [XM], then inside it we would define [FXM := F XM] and then start another inner module taking the extra parameters [sM] and [HM], whose types depend on [FXM] having a name. *)
  Module inF_from_F_section_M (XM : TypeM) (FXM : Comodality InF XM)
    (sM : FunctionM XM FXM) (HM : SectM XM FXM sM FXM.fromM)
  : InM InF XM.
    (** Boilerplate *)
    Module s_o_from_M <: FunctionM FXM FXM
      := ComposeM FXM.mM XM FXM sM FXM.fromM.
    Module idmap_FXM := IdmapM FXM.
    (** We intend to apply [coindpaths] to show that the composite of [s] and [from F X] in the other order is also the identity.  The following sort of boilerplate will be required whenever we apply [coindpaths]. *)
    Module coindpaths_retr_M
      := FXM.coindpathsM FXM FXM.isinF_mM s_o_from_M idmap_FXM.
    Module coindpaths_retr_p_M
    : HomotopyM FXM XM coindpaths_retr_M.domM coindpaths_retr_M.codM.
      Definition m : FXM.fromM.m o sM.m o FXM.fromM.m == FXM.fromM.m
        := fun x => HM.m (FXM.fromM.m x).
    End coindpaths_retr_p_M.
    Module coindpaths_retr_M_mM
      := coindpaths_retr_M.mM coindpaths_retr_p_M.
    (** Using this, we can show that [X] is equivalent to [F X]. *)
    Module equiv_fromF_M : EquivM FXM XM.
      Definition m : FXM.m -> XM.m
        := FXM.from.
      Definition m_isequiv : IsEquiv m.
      Proof.
        refine (isequiv_adjointify FXM.from sM.m HM.m _).
        apply (coindpaths_retr_M_mM.m).
      Defined.
    End equiv_fromF_M.
    (** Finally, we apply repleteness to this equivalence. *)
    Module mM := FXM.repleteM XM equiv_fromF_M.
    Include mM.
  End inF_from_F_section_M.

  (** The preceding is our first example of a module-level theorem and proof; we will see many more below.  In general, such module-proofs are very much like ordinary proofs, but with additional verbosity and boilerplate, coming mainly from the fact that all modules must be given names before we can access their fields. *)

  (** ** Comodal types are closed under colimits *)

  (** *** The empty type *)

  (** As we expect (since coreflective subcategories are closed under colimits), [Empty] lies in [F]. *)
  Module isinF_Empty_M : InM InF EmptyM.
    (** As mentioned above, we use a coreflection of [EmptyM], but it doesn't matter which one, since the end result "[Empty] lies in [F]" makes no reference to the coreflection.  Thus, we can apply [F] without any trouble.  The same reasoning will apply to the other similar proofs below. *)
    Module FEmptyM := F EmptyM.
    Module sM : FunctionM EmptyM FEmptyM.
      Definition m : EmptyM.m@{i j} -> FEmptyM.m@{i j}
        := Empty_rec@{i i} _.
    End sM.
    Module HM : SectM EmptyM FEmptyM sM FEmptyM.fromM.
      Definition m : Sect sM.m FEmptyM.fromM.m := Empty_ind _.
    End HM.
    Module mM := inF_from_F_section_M EmptyM FEmptyM sM HM.
    Include mM.
  End isinF_Empty_M.

  (** *** Sum types *)

  (** Similarly, [F] is closed under sums. *)
  Module isinF_Sum_M (XM : TypeM) (YM : TypeM)
         (isinF_XM : InM InF XM) (isinF_YM : InM InF YM)
         (FXM : Comodality InF XM) (FYM : Comodality InF YM).
    Module SM := SumM XM YM.
    Module FSM := F SM.
    Module inlM <: FunctionM XM SM.
      Definition m := inl : XM.m -> SM.m.
    End inlM.
    Module inrM <: FunctionM YM SM.
      Definition m := inr : YM.m -> SM.m.
    End inrM.
    (** We could construct the section indirectly using functoriality of the coreflector, but it's easier just to apply the corecursion principle in one swell foop.  *)
    Module slM := FSM.corecM XM isinF_XM inlM.
    Module srM := FSM.corecM YM isinF_YM inrM.
    Module sM <: FunctionM SM FSM.
      Definition m (xy : SM.m) : FSM.m
        := match xy with
             | inl x => slM.m x
             | inr y => srM.m y
           end.
    End sM.
    Module HM <: SectM SM FSM sM FSM.fromM.
      Definition m : Sect sM.m FSM.fromM.m.
      Proof.
        intros [x|y].
        - apply slM.m_beta.
        - apply srM.m_beta.
      Defined.
    End HM.
    Module mM : InM InF SM
      := inF_from_F_section_M SM FSM sM HM.
    (** We can't give this one a completely toplevel name, since it requires defining [SumM XM YM] inside a module after [XM] and [YM] have been hypothesized. *)
  End isinF_Sum_M.

  (** *** Bool *)

  (** In particular, if [F] contains [Unit], then it also contains [Bool].  It's easier to prove this directly than derive it from [Bool <~> Unit + Unit]. *)
  Module isinF_Bool_M (isinF_UnitM : InF_Unit_M InF).
    Module FBoolM := F BoolM.
    Module trueM <: FunctionM UnitM BoolM.
      Definition m : UnitM.m -> BoolM.m := fun _ => true.
    End trueM.
    Module falseM <: FunctionM UnitM BoolM.
      Definition m : UnitM.m -> BoolM.m := fun _ => false.
    End falseM.
    Module stM := FBoolM.corecM UnitM isinF_UnitM trueM.
    Module sfM := FBoolM.corecM UnitM isinF_UnitM falseM.
    Module sM <: FunctionM BoolM FBoolM.
      Definition m (b : BoolM.m) : FBoolM.m
        := if b then (stM.m tt) else (sfM.m tt).
    End sM.
    Module HM <: SectM BoolM FBoolM sM FBoolM.fromM.
      Definition m : Sect sM.m FBoolM.fromM.m.
      Proof.
        intros [|].
        - apply stM.m_beta.
        - apply sfM.m_beta.
      Defined.
    End HM.
    Module mM : InM InF BoolM
      := inF_from_F_section_M BoolM FBoolM sM HM.
  End isinF_Bool_M.

  (** *** Nat *)

  (** Although [nat] is not necessarily an external colimit, the same arguments work for it. *)
  Module isinF_Nat_M (isinF_UnitM : InF_Unit_M InF).
    Module FNatM := F NatM.
    Module zeroM <: FunctionM UnitM NatM.
      Definition m : UnitM.m@{i j} -> NatM.m@{i j} := fun _ => 0.
    End zeroM.
    Module succM <: FunctionM NatM NatM.
      Definition m : NatM.m@{i j} -> NatM.m@{i j} := S.
    End succM.
    Module szM := FNatM.corecM UnitM isinF_UnitM zeroM.
    Module succ_o_fromM <: FunctionM FNatM NatM
      := ComposeM FNatM NatM NatM succM FNatM.fromM.
    Module ssM := FNatM.corecM FNatM FNatM.isinF_mM succ_o_fromM.
    Module sM <: FunctionM NatM FNatM.
      Definition m (n : NatM.m) : FNatM.m.
      Proof.
        induction n as [|n IH].
        - exact (szM.m tt).
        - exact (ssM.m IH).
      Defined.
    End sM.
    Module HM <: SectM NatM FNatM sM FNatM.fromM.
      Definition m : Sect sM.m FNatM.fromM.m.
      Proof.
        intros n; induction n as [|n IH].
        - apply szM.m_beta.
        - refine (ssM.m_beta _ @ ap S IH).
      Defined.
    End HM.
    Module mM : InM InF NatM
      := inF_from_F_section_M NatM FNatM sM HM.
  End isinF_Nat_M.

  (** ** Functoriality *)

  (** Functoriality of the coreflector.  Here we do hypothesize arbitrary coreflections, since the conclusion is a function between the coreflections, and we may want to apply it as a lemma during some other development. *)
  Module the_F_functor_M (XM YM : TypeM) (fM : FunctionM XM YM)
         (FXM : Comodality InF XM) (FYM : Comodality InF YM)
      <: FunctionM FXM FYM.
    Module f_o_from_M <: FunctionM FXM.mM YM.
      Definition m := fM.m o FXM.from.
    End f_o_from_M.
    Module mM := FYM.corecM FXM.mM FXM.isinF_mM f_o_from_M.
    (** This next definition means that an instantiation of [F_functor_M XM YM fM FXM FYM] can be typed as [FunctionM FXM FYM]. *)
    Definition m := mM.m.
    (** Note that [mM.m_beta] is the naturality of [from]. *)
    Definition from_natural := mM.m_beta.
  End the_F_functor_M.

  (** In fact, the problem that module functions are productive afflicts functoriality directly as well: because the functorial action is defined by applying the hypothesized module function [corecM], applying it twice in different places yields different results.  Thus, when proving additional things about functoriality, we need to be able to hypothesize arbitrary values of [F] on morphisms as well. *)
  Module Type F_functor_M (XM YM : TypeM) (fM : FunctionM XM YM)
         (FXM : Comodality InF XM) (FYM : Comodality InF YM)
  <: FunctionM FXM FYM.
    (** The body of this module type looks just like [the_F_functor_M], except that instead of applying "the" corecursor, we assume an arbitrary one.  Thus, [the_F_functor_M] is an instantiation of this module type, and conversely a hypothesized instantiation of this module type can generally be dropped anywhere in place of [the_F_functor_M]. *)
    Module f_o_from_M <: FunctionM FXM.mM YM.
      Definition m := fM.m o FXM.from.
    End f_o_from_M.
    Declare Module mM : CorecM InF FYM YM FYM.fromM FXM FXM.isinF_mM f_o_from_M.
    Definition m := mM.m.
    Definition from_natural := mM.m_beta.
  End F_functor_M.

  (** Functoriality acting on composition. *)
  Module F_functor_compose_M (XM YM ZM : TypeM)
         (gM : FunctionM YM ZM) (fM : FunctionM XM YM)
         (FXM : Comodality InF XM) (FYM : Comodality InF YM)
         (FZM : Comodality InF ZM)
         (FgM : F_functor_M YM ZM gM FYM FZM)
         (FfM : F_functor_M XM YM fM FXM FYM).
    Module Fg_o_Ff_M <: FunctionM FXM FZM
      := ComposeM FXM FYM FZM FgM FfM.
    Module gfM <: FunctionM XM ZM
      := ComposeM XM YM ZM gM fM.
    Module mM (FgfM : F_functor_M XM ZM gfM FXM FZM)
        <: HomotopyM FXM FZM Fg_o_Ff_M FgfM.
      Module cipM := FZM.coindpathsM FXM FXM.isinF_mM Fg_o_Ff_M FgfM.
      Module HM <: HomotopyM FXM ZM cipM.domM cipM.codM.
        Definition m : cipM.domM.m == cipM.codM.m.
        Proof.
          intros x.
          unfold cipM.domM.m, cipM.codM.m.
          unfold Fg_o_Ff_M.m, FgfM.m.
          refine (FgM.from_natural (FfM.m x) @ _).
          unfold FgM.f_o_from_M.m.
          refine (ap gM.m (FfM.from_natural x) @ _).
          unfold FfM.f_o_from_M.m.
          refine (_ @ (FgfM.from_natural x)^).
          unfold FgfM.f_o_from_M.m.
          reflexivity.
        Defined.
      End HM.
      Module mM := cipM.mM HM.
      Definition m : Fg_o_Ff_M.m == FgfM.m := mM.m.
    End mM.
  End F_functor_compose_M.

  (** And identities *)
  Module F_functor_idmap_M (XM : TypeM) (FXM : Comodality InF XM).
    Module idmapXM := IdmapM XM.
    Module idmapFXM := IdmapM FXM.
    Module mM (FidmapXM : F_functor_M XM XM idmapXM FXM FXM)
        <: HomotopyM FXM FXM idmapFXM FidmapXM.
      Module cipM := FXM.coindpathsM FXM FXM.isinF_mM idmapFXM FidmapXM.
      Module HM <: HomotopyM FXM XM cipM.domM cipM.codM.
        Definition m : cipM.domM.m == cipM.codM.m.
        Proof.
          intros x.
          unfold cipM.domM.m, cipM.codM.m.
          unfold idmapFXM.m.
          symmetry; apply FidmapXM.from_natural.
        Defined.
      End HM.
      Module mM := cipM.mM HM.
      Definition m : idmapFXM.m == FidmapXM.m := mM.m.
    End mM.
  End F_functor_idmap_M.

  (** 2-Functoriality *)
  Module F_functor_homotopy_M
         (XM YM : TypeM)
         (fM gM : FunctionM XM YM)
         (HM : HomotopyM XM YM fM gM)
         (FXM : Comodality InF XM) (FYM : Comodality InF YM)
         (FfM : F_functor_M XM YM fM FXM FYM)
         (FgM : F_functor_M XM YM gM FXM FYM)
      <: HomotopyM FXM FYM FfM FgM.
    Module cipM := FYM.coindpathsM FXM FXM.isinF_mM FfM FgM.
    Module from_HM <: HomotopyM FXM YM cipM.domM cipM.codM.
      Definition m : cipM.domM.m == cipM.codM.m.
      Proof.
        intros x.
        unfold cipM.domM.m, cipM.codM.m.
        refine (FfM.from_natural x @ _).
        refine (_ @ (FgM.from_natural x)^).
        unfold FfM.f_o_from_M.m, FgM.f_o_from_M.m.
        exact (HM.m (FXM.from x)).
      Defined.
    End from_HM.
    Module mM := cipM.mM from_HM.
    Definition m : FfM.m == FgM.m := mM.m.
  End F_functor_homotopy_M.

  (** We state separately 2-functoriality on sections. *)
  Module F_functor_sect_M
         (XM YM : TypeM)
         (sM : FunctionM XM YM) (rM : FunctionM YM XM)
         (HM : SectM XM YM sM rM)
         (FXM : Comodality InF XM) (FYM : Comodality InF YM)
         (FsM : F_functor_M XM YM sM FXM FYM)
         (FrM : F_functor_M YM XM rM FYM FXM)
      <: SectM FXM FYM FsM FrM.
    (** We apply functoriality on composition *)
    Module Ffc_rsM := F_functor_compose_M XM YM XM rM sM FXM FYM FXM FrM FsM.
    Module rsM := Ffc_rsM.gfM.
    Module FrFsM := Ffc_rsM.Fg_o_Ff_M.
    Module Ff_rsM := the_F_functor_M XM XM rsM FXM FXM.
    Module FrsM := Ffc_rsM.mM Ff_rsM.
    (** And functoriality on the identity *)
    Module Ffi_XM := F_functor_idmap_M XM FXM.
    Module iXM := Ffi_XM.idmapXM.
    Module Ff_iXM := the_F_functor_M XM XM iXM FXM FXM.
    Module FfiXM := Ffi_XM.mM Ff_iXM.
    (** And 2-functoriality on the homotopy *)
    Module FsectM := F_functor_homotopy_M XM XM rsM iXM HM FXM FXM Ff_rsM Ff_iXM.
    (** Finally, we construct the section homotopy. *)
    Module mM <: SectM FXM FYM FsM FrM.
      Definition m : Sect FsM.m FrM.m.
      Proof.
        intros x.
        refine (FrsM.m x @ _).
        refine (FsectM.m x @ _).
        refine (FfiXM.m x)^.
      Defined.
    End mM.
    Definition m : Sect FsM.m FrM.m := mM.m.
  End F_functor_sect_M.         

  (** Functoriality preserves equivalences. *)
  Module F_functor_isequiv_M
           (XM YM : TypeM) (fM : FunctionM XM YM)
           (eM : IsEquivM XM YM fM)
           (FXM : Comodality InF XM) (FYM : Comodality InF YM)
           (FfM : F_functor_M XM YM fM FXM FYM)
      <: IsEquivM FXM FYM FfM.
    Instance isequiv_f : IsEquiv fM.m := eM.m.
    Module invM <: FunctionM YM XM.
      Definition m : YM.m -> XM.m := fM.m^-1.
    End invM.
    Module eissectM <: SectM XM YM fM invM.
      Definition m : Sect fM.m invM.m := eissect fM.m.
    End eissectM.
    Module eisretrM <: SectM YM XM invM fM.
      Definition m : Sect invM.m fM.m := eisretr fM.m.
    End eisretrM.
    Module FinvM := the_F_functor_M YM XM invM FYM FXM.
    Module FissectM := F_functor_sect_M XM YM fM invM eissectM FXM FYM FfM FinvM.
    Module FisretrM := F_functor_sect_M YM XM invM fM eisretrM FYM FXM FinvM FfM.
    Definition m : IsEquiv FfM.m
      := isequiv_adjointify _ FinvM.m FisretrM.mM.m FissectM.mM.m.
  End F_functor_isequiv_M.

  (** If [X] lies in [F], then [from F X] is an equivalence. *)
  Module from_F_isequiv_M (XM : TypeM) (isinF_XM : InM InF XM)
         (FXM : Comodality InF XM)
      <: IsEquivM FXM XM FXM.fromM.
    Module idmap_XM := IdmapM XM.
    Module invM := FXM.corecM XM isinF_XM idmap_XM.
    (** [invM.m] is the inverse function, [invM.m_beta] is its [eisretr].  To prove [eissect], we use [coindpaths]. *)
    Module idmap_FXM := IdmapM FXM.mM.
    Module inverse_o_from_M
      := ComposeM FXM.mM XM FXM.mM invM FXM.fromM.
    Module cipM := FXM.coindpathsM FXM.mM FXM.isinF_mM
                                   inverse_o_from_M idmap_FXM.
    Module HM <: HomotopyM FXM.mM XM cipM.domM cipM.codM.
      Definition m : FXM.fromM.m o invM.m o FXM.fromM.m == FXM.fromM.m
        := fun x => invM.m_beta (FXM.fromM.m x).
    End HM.
    Module issectM := cipM.mM HM.
    Definition m : IsEquiv FXM.fromM.m
      := isequiv_adjointify _ invM.m invM.m_beta issectM.m.
  End from_F_isequiv_M.

  (** ** The coreflector preserves limits *)

  (** Since the coreflector is a right adjoint, it preserves limits.  More precisely, it takes limits of types to limits *in the subuniverse*, which might not agree with the ambient limits.  However, they do if the subuniverse is closed under a particular kind of limit. *)

  (** *** Products *)

  Module isequiv_F_prod_cmp_M (isinF_prod_M : InF_Prod_M InF)
         (** forall *)
         (XM YM : TypeM)
         (FXM : Comodality InF XM) (FYM : Comodality InF YM).
    (** We define the comparison map that we will show to be an equivalence. *)
    Module PM := ProdM XM YM.
    Module PFM := ProdM FXM FYM.
    Module fstM <: FunctionM PM XM.
      Definition m := @fst XM.m YM.m.
    End fstM.
    Module sndM <: FunctionM PM YM.
      Definition m := @snd XM.m YM.m.
    End sndM.
    Module FPM := F PM.
    Module FfstM <: FunctionM FPM FXM
      := the_F_functor_M PM XM fstM FPM FXM.
    Module FsndM <: FunctionM FPM FYM
      := the_F_functor_M PM YM sndM FPM FYM.
    Module cmpM <: FunctionM FPM PFM.
      Definition m : FPM.m -> PFM.m
        := fun z => (FfstM.m z , FsndM.m z).
    End cmpM.
    (** We use the hypothesis *)
    Module isinF_PFM : InM InF PFM
      := isinF_prod_M FXM FYM FXM.isinF_mM FYM.isinF_mM.
    (** We construct an inverse to it using corecursion. *)
    Module prod_from_M <: FunctionM PFM PM.
      Definition m : PFM.m -> PM.m
        := fun z => ( FXM.from (fst z) , FYM.from (snd z) ).
    End prod_from_M.
    Module cmpinvM <: FunctionM PFM FPM
      := FPM.corecM PFM isinF_PFM prod_from_M.
    (** We prove the first homotopy *)
    Module cmpinv_o_cmp_M <: FunctionM FPM FPM
      := ComposeM FPM PFM FPM cmpinvM cmpM.
    Module idmap_FPM <: FunctionM FPM FPM
      := IdmapM FPM.
    Module cip_FPM := FPM.coindpathsM FPM FPM.isinF_mM
                                      cmpinv_o_cmp_M idmap_FPM.
    Module cip_FPHM <: HomotopyM FPM PM cip_FPM.domM cip_FPM.codM.
      Definition m : cip_FPM.domM.m@{i j} == cip_FPM.codM.m@{i j}.
      Proof.
        intros x.
        unfold cip_FPM.domM.m, cmpinv_o_cmp_M.m.
        unfold cip_FPM.codM.m, idmap_FPM.m.
        refine (cmpinvM.m_beta@{i j} (cmpM.m@{i j} x) @ _).
        unfold prod_from_M.m, FPM.fromM.m.
        unfold cmpM.m; simpl.
        apply path_prod@{i i i}; simpl.
        - exact (FfstM.mM.m_beta@{i j} x).
        - exact (FsndM.mM.m_beta@{i j} x).
      Defined.
    End cip_FPHM.
    Module cmp_issect_M
      <: HomotopyM FPM FPM cmpinv_o_cmp_M idmap_FPM
      := cip_FPM.mM cip_FPHM.
    (** And the second homotopy *)
    Module fstFM <: FunctionM PFM FXM.
      Definition m := @fst FXM.m FYM.m.
    End fstFM.
    Module sndFM <: FunctionM PFM FYM.
      Definition m := @snd FXM.m FYM.m.
    End sndFM.
    (** This takes separate proofs for the two halves *)
    Module fst_o_cmpinv_M <: FunctionM PFM FXM
      := ComposeM PFM FPM FXM FfstM cmpinvM.
    Module cip_FXM := FXM.coindpathsM PFM isinF_PFM fst_o_cmpinv_M fstFM.
    Module cip_FXHM <: HomotopyM PFM XM cip_FXM.domM cip_FXM.codM.
      Definition m : cip_FXM.domM.m@{i j} == cip_FXM.codM.m@{i j}.
      Proof.
        intros [a b].
        unfold cip_FXM.domM.m, cip_FXM.codM.m.
        unfold fst_o_cmpinv_M.m, fstFM.m; simpl.
        refine (FfstM.from_natural _ @ _).
        unfold FfstM.f_o_from_M.m.
        refine (ap fst (cmpinvM.m_beta (a,b)) @ _).
        unfold prod_from_M.m; simpl. reflexivity.
      Defined.
    End cip_FXHM.
    Module cmp_isretr_fst_M <: HomotopyM PFM FXM fst_o_cmpinv_M fstFM
      := cip_FXM.mM cip_FXHM.
    (** Now the second half *)
    Module snd_o_cmpinv_M <: FunctionM PFM FYM
      := ComposeM PFM FPM FYM FsndM cmpinvM.
    Module cip_FYM := FYM.coindpathsM PFM isinF_PFM snd_o_cmpinv_M sndFM.
    Module cip_FYHM <: HomotopyM PFM YM cip_FYM.domM cip_FYM.codM.
      Definition m : cip_FYM.domM.m@{i j} == cip_FYM.codM.m@{i j}.
      Proof.
        intros [a b].
        unfold cip_FYM.domM.m, cip_FYM.codM.m.
        unfold snd_o_cmpinv_M.m, sndFM.m; simpl.
        refine (FsndM.from_natural _ @ _).
        unfold FsndM.f_o_from_M.m.
        refine (ap snd (cmpinvM.m_beta (a,b)) @ _).
        unfold prod_from_M.m; simpl. reflexivity.
      Defined.
    End cip_FYHM.
    Module cmp_isretr_snd_M <: HomotopyM PFM FYM snd_o_cmpinv_M sndFM
      := cip_FYM.mM cip_FYHM.
    (** And finally the equivalence *)
    Definition m : IsEquiv cmpM.m.
    Proof.
      refine (isequiv_adjointify _ cmpinvM.m _ cmp_issect_M.m).
      intros [a b]; apply path_prod'.
      - apply cmp_isretr_fst_M.m.
      - apply cmp_isretr_snd_M.m.
    Defined.
    (** Thus, this module can be duck-typed as [IsEquivM cmpM], although we couldn't declare it that way with [<:] since [cmpM] is only defined inside the module. *)
  End isequiv_F_prod_cmp_M.

  (** It follows that in this case, the coreflector also preserves hprops. *)
  Module ishprop_F_M (isinF_prod_M : InF_Prod_M InF)
         (** forall *)
         (XM : TypeM) (hpXM : IsHPropM XM) (FXM : Comodality InF XM)
  : IsHPropM FXM.
    Module iFpcM := isequiv_F_prod_cmp_M isinF_prod_M XM XM FXM FXM.
    (** About the diagonal *)
    Module diagM <: FunctionM XM iFpcM.PM.
      Definition m : XM.m -> iFpcM.PM.m
        := fun x => (x,x).
    End diagM.
    Module isequiv_diagM <: IsEquivM XM iFpcM.PM diagM.
      Definition m : IsEquiv diagM.m.
      Proof.
        apply isequiv_diag_ishprop.
      Defined.
    End isequiv_diagM.
    Module FdiagM := the_F_functor_M XM iFpcM.PM diagM FXM iFpcM.FPM.
    Module isequiv_FdiagM
      := F_functor_isequiv_M XM iFpcM.PM diagM isequiv_diagM
                             FXM iFpcM.FPM FdiagM.
    (** About the identity *)
    Module idmapXM := IdmapM XM.
    Module FidmapXM := the_F_functor_M XM XM idmapXM FXM FXM.
    Module FfiXM := F_functor_idmap_M XM FXM.
    Module FfiXM' := FfiXM.mM FidmapXM.
    (** About [fst o diag] *)
    Module Ffc_fst_diag_M
      := F_functor_compose_M XM iFpcM.PM XM iFpcM.fstM diagM
                             FXM iFpcM.FPM FXM iFpcM.FfstM FdiagM.
    Module F_fst_diag_M
      := the_F_functor_M XM XM Ffc_fst_diag_M.gfM FXM FXM.
    Module Ffc_fst_diag_M' := Ffc_fst_diag_M.mM F_fst_diag_M.
    Module fst_diag_idmap_M
      <: HomotopyM XM XM Ffc_fst_diag_M.gfM idmapXM.
      Definition m : Ffc_fst_diag_M.gfM.m == idmapXM.m
        := fun x => 1.
    End fst_diag_idmap_M.
    Module F_fst_diag_idmap_M
      := F_functor_homotopy_M XM XM Ffc_fst_diag_M.gfM idmapXM
                              fst_diag_idmap_M
                              FXM FXM F_fst_diag_M FidmapXM.
    (** About [snd o diag] *)
    Module Ffc_snd_diag_M
      := F_functor_compose_M XM iFpcM.PM XM iFpcM.sndM diagM
                             FXM iFpcM.FPM FXM iFpcM.FsndM FdiagM.
    Module F_snd_diag_M
      := the_F_functor_M XM XM Ffc_snd_diag_M.gfM FXM FXM.
    Module Ffc_snd_diag_M' := Ffc_snd_diag_M.mM F_snd_diag_M.
    Module snd_diag_idmap_M
      <: HomotopyM XM XM Ffc_snd_diag_M.gfM idmapXM.
      Definition m : Ffc_snd_diag_M.gfM.m == idmapXM.m
        := fun x => 1.
    End snd_diag_idmap_M.
    Module F_snd_diag_idmap_M
      := F_functor_homotopy_M XM XM Ffc_snd_diag_M.gfM idmapXM
                              snd_diag_idmap_M
                              FXM FXM F_snd_diag_M FidmapXM.
    Definition m : IsHProp FXM.m.
    Proof.
      apply @ishprop_isequiv_diag.
      refine (isequiv_homotopic (iFpcM.cmpM.m o FdiagM.m) _).
      - apply @isequiv_compose.
        + apply isequiv_FdiagM.m.
        + apply iFpcM.m.
      - intros x.
        unfold iFpcM.cmpM.m; apply path_prod'.
        + refine (Ffc_fst_diag_M'.m x @ _).
          refine (F_fst_diag_idmap_M.m x @ _).
          refine (FfiXM'.m x)^.
        + refine (Ffc_snd_diag_M'.m x @ _).
          refine (F_snd_diag_idmap_M.m x @ _).
          refine (FfiXM'.m x)^.
    Defined.
  End ishprop_F_M.

End Comodality_Theory.

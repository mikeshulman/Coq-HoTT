Require Import Basics.
Require Import Types.
Require Import Pointed.Core.

Local Open Scope pointed_scope.

(** Some higher homotopies *)

Definition phomotopy_compose_h1 {A : pType} {P : pFam A} {f g : pForall A P}
 (p : f ==* g) : p @* reflexivity g ==* p.
Proof.
  serapply Build_pHomotopy.
  + intro x. apply concat_p1.
  + pointed_reduce. 
    rewrite (concat_pp_V H (concat_p1 _))^. generalize (H @ concat_p1 _). 
    clear H. intros H. destruct H.
    generalize (p ispointed_type). generalize (g ispointed_type).
    intros x q. destruct q. reflexivity.
Defined.

Definition phomotopy_compose_1h {A : pType} {P : pFam A} {f g : pForall A P}
 (p : f ==* g) : reflexivity f @* p ==* p.
Proof.
  serapply Build_pHomotopy.
  + intro x. apply concat_1p.
  + pointed_reduce. 
    rewrite (concat_pp_V H (concat_p1 _))^. generalize (H @ concat_p1 _). 
    clear H. intros H. destruct H.
    generalize (p ispointed_type). generalize (g ispointed_type).
    intros x q. destruct q. reflexivity.
Defined.

Definition phomotopy_inverse_1 {A : pType} {P : pFam A} {f : pForall A P}
  : (phomotopy_reflexive f) ^* ==* phomotopy_reflexive f.
Proof.
  serapply Build_pHomotopy.
  + reflexivity.
  + pointed_reduce. reflexivity.
Defined.

(** [phomotopy_path] sends concatenation to composition of pointed homotopies.*)
Definition phomotopy_path_pp `{Funext} {A : pType} {P : pFam A} 
  {f g h : pForall A P} (p : f = g) (q : g = h)
  : phomotopy_path (p @ q) ==* phomotopy_path p @* phomotopy_path q.
Proof.
  induction p. induction q. symmetry. apply phomotopy_compose_h1.
Defined.

(** [phomotopy_path] sends inverses to inverses.*)
Definition phomotopy_path_V `{Funext} {A : pType} {P : pFam A} 
  {f g : pForall A P} (p : f = g)
  : phomotopy_path (p^) ==* (phomotopy_path p)^*.
Proof.
  induction p. simpl. symmetry. apply phomotopy_inverse_1.
Defined.

Definition phomotopy_hcompose `{Funext} {A : pType} {P : pFam A} {f g h : pForall A P}
 {p p' : f ==* g} {q q' : g ==* h} (r : p ==* p') (s : q ==* q') : 
  p @* q ==* p' @* q'.
Proof.
  serapply Build_pHomotopy.
  + intro x. exact (r x @@ s x). 
  + revert q' s. serapply phomotopy_ind.
    revert p' r. serapply phomotopy_ind.
    revert h q.  serapply phomotopy_ind.
    revert g p.  serapply phomotopy_ind.
    pointed_reduce. reflexivity.
Defined.

Reserved Infix "@@*" (at level 30).
Notation "p @@* q" := (phomotopy_hcompose p q).

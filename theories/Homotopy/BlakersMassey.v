Require Import HoTT.Basics HoTT.Types HoTT.HIT.Pushout HoTT.HIT.Join.
Require Import HoTT.Modalities.Modality.

(* Some path algebra lemmas that I can't be bothered to prove at the
moment. *)

Definition foo {A : Type} {x y : A} (p q : x = y) (r : p @ p^ = q @ p^)
  : moveR_1M _ _ ((concat_pV p)^ @ r)
    = cancelR p q p^ r.
Proof.
  (* Annoying path algebra *)
Admitted.

Definition bar {A : Type} {x y : A} (p q : x = y) (s : p = q)
  : concat_pV p @ moveL_pV p 1 q (concat_1p p @ s)
    = whiskerR s p^.
Proof.
  (* Annoying path algebra *)
Admitted.

Module BlakersMassey (Os : Modalities).
  Import Os.
  Module Import Os_Theory := Modalities_Theory Os.

  Section GBM.
    Context `{Univalence} {X Y : Type} (Q : X -> Y -> Type).

    (* First we define pushouts of "dependent spans", as in the HFLL
    paper, in terms of our pushouts of functions, and derive their
    induction principle. *)

    Definition spushout := @pushout {xy:X * Y & Q (fst xy) (snd xy)} X Y
                                    (fst o pr1) (snd o pr1).
    Definition spushl : X -> spushout := pushl.
    Definition spushr : Y -> spushout := pushr.
    Definition sglue {x:X} {y:Y} : Q x y -> spushl x = spushr y
      := fun q => pp ((x,y) ; q).

    Definition spushout_rec (R : Type)
               (spushl' : X -> R) (spushr' : Y -> R)
               (sglue' : forall x y (q : Q x y), spushl' x = spushr' y)
      : spushout -> R.
    Proof.
      srapply (@pushout_rec {xy:X * Y & Q (fst xy) (snd xy)} X Y
                            (fst o pr1) (snd o pr1) R spushl' spushr').
      intros [[x y] q]; cbn in *.
      apply sglue'; assumption.
    Defined.

    Definition spushout_ind (R : spushout -> Type)
               (spushl' : forall x, R (spushl x))
               (spushr' : forall y, R (spushr y))
               (sglue' : forall x y (q : Q x y), 
                   transport R (sglue q) (spushl' x) = (spushr' y))
      : forall p, R p.
    Proof.
      srapply (@pushout_ind {xy:X * Y & Q (fst xy) (snd xy)} X Y
                            (fst o pr1) (snd o pr1) R spushl' spushr').
      intros [[x y] q]; cbn in *.
      apply sglue'; assumption.
    Defined.

    (* Here's the hypothesis of ABFJ generalized Blakers-Massey. *)

    Context (O : Modality).
    Context
      (isconnected_cogap : 
         forall (x1 x3 : X) (y2 y4 : Y)
                (q12 : Q x1 y2) (q32 : Q x3 y2) (q34 : Q x3 y4),
           IsConnected O (join ((x1;q12) = (x3;q32) :> {x:X & Q x y2})
                               ((y2;q32) = (y4;q34) :> {y:Y & Q x3 y}))).

    Definition code (x0 : X) (y0 : Y) (q00 : Q x0 y0)
      : forall (p : spushout), (spushl x0 = p) -> Type.
    Proof.
      srapply spushout_ind; [ intros x r | intros y r | ]; cbn.
      { exact (O (hfiber (fun q10 => sglue q00 @ (sglue q10)^) r)). }
      { exact (O (hfiber sglue r)). }
      intros x1 y1 q11.
      apply path_arrow; intros r.
      rewrite transport_arrow_toconst, transport_paths_r; unfold hfiber.
      apply path_universe_uncurried; srefine (equiv_adjointify _ _ _ _).
      1,2:apply O_rec.
      { intros [q10 s].
        refine (@isconnected_elim
                  O _ (isconnected_cogap x0 x1 y0 y1 q00 q10 q11) _ _ _).1.
        srefine (pushout_rec _ _ _ _).
        (* I don't know whether this is the best approach, but at the
        moment it seems easier to me to arrange things to use J over
        and over rather than mucking through all the path algebra. *)
        - intros e.
          set (xq := (x0 ; q00)) in *.
          change (spushl xq.1 = spushr y1) in r.
          change (sglue xq.2 @ (sglue q10)^ = r @ (sglue q11)^) in s.
          change (O {q01 : Q xq.1 y1 & sglue q01 = r}).
          clearbody xq; clear x0 q00.
          symmetry in e; destruct e; cbn in *.
          apply to.
          exists q11.
          exact (moveR_1M _ _ ((concat_pV (sglue q10))^ @ s)).
        - intros e.
          set (yq := (y1 ; q11)) in *.
          change (spushl x0 = spushr yq.1) in r.
          change (sglue q00 @ (sglue q10)^ = r @ (sglue yq.2)^) in s.
          change (O {q01 : Q x0 yq.1 & sglue q01 = r}).
          clearbody yq; clear y1 q11.
          destruct e; cbn in *.
          apply to.
          exists q00.
          exact (cancelR _ _ _ s).
        - cbn.
          intros [ex ey].
          set (xq := (x0 ; q00)) in *.
          set (yq := (y1 ; q11)) in *.
          change (spushl xq.1 = spushr yq.1) in r.
          change (sglue xq.2 @ (sglue q10)^ = r @ (sglue yq.2)^) in s.
          rewrite <- (inv_V ex). (* May need to replace that *)
          set (ex' := ex^).
          clearbody ex'. clear ex.
          (* There must be a better way to say "replace x0, q00, y1,
          and y11 everywhere in the conclusion with the definitionally
          equal terms xq.1, xq.2, yq.1, and yq.2. *)
          change (match
                     match ex'^ in (_ = y) return (y = xq) with
                     | idpath => idpath
                     end in (_ = y)
                     return
                     (forall r0 : spushl (pr1 y) = spushr yq.1,
                         sglue (pr2 y) @ (sglue q10)^ = r0 @ (sglue yq.2)^ ->
                         O {q01 : Q (pr1 y) yq.1 & sglue q01 = r0})
                   with
                   | idpath =>
                     fun (r0 : spushl x1 = spushr yq.1)
                         (s0 : sglue q10 @ (sglue q10)^ = r0 @ (sglue yq.2)^) =>
                       to O {q01 : Q x1 yq.1 & sglue q01 = r0}
                          (yq.2; moveR_1M (sglue yq.2) r0 ((concat_pV (sglue q10))^ @ s0))
                   end r s =
                  match
                    ey in (_ = y)
                    return
                    (forall r0 : spushl xq.1 = spushr (pr1 y),
                        sglue xq.2 @ (sglue q10)^ = r0 @ (sglue (pr2 y))^ ->
                        O {q01 : Q xq.1 (pr1 y) & sglue q01 = r0})
                  with
                  | idpath =>
                    fun (r0 : spushl xq.1 = spushr y0)
                        (s0 : sglue xq.2 @ (sglue q10)^ = r0 @ (sglue q10)^) =>
                      to O {q01 : Q xq.1 y0 & sglue q01 = r0}
                         (xq.2; cancelR (sglue xq.2) r0 (sglue q10)^ s0)
                  end r s
                 ).
          clearbody xq yq. clear x0 q00 y1 q11.
          destruct ey, ex'. cbn in *.
          apply ap; apply ap.
          apply foo. }
      { intros [q01 s].
        refine (@isconnected_elim
                  O _ (isconnected_cogap x1 x0 y1 y0 q11 q01 q00) _ _ _).1.
        srefine (pushout_rec _ _ _ _).
        - intros e. 
          set (xq := (x1 ; q11)) in *.
          change (O {q10 : Q xq.1 y0 & sglue q00 @ (sglue q10)^ = r @ (sglue xq.2)^}).
          clearbody xq; clear x1 q11.
          symmetry in e; destruct e; cbn in *.
          apply to.
          exists q00.
          refine (concat_pV _ @ _).
          apply moveL_pV.
          exact (concat_1p _ @ s).
        - intros e.
          set (yq := (y0 ; q00)) in *.
          change (O {q10 : Q x1 yq.1 & sglue yq.2 @ (sglue q10)^ = r @ (sglue q11)^}).
          clearbody yq; clear y0 q00.
          destruct e; cbn in *.
          apply to.
          exists q11.
          apply whiskerR; exact s.
        - cbn.
          intros [ex ey].
          set (xq := (x1 ; q11)) in *.
          set (yq := (y0 ; q00)) in *.
          rewrite <- (inv_V ex). (* May need to replace that *)
          set (ex' := ex^).
          clearbody ex'. clear ex. 
          change (match
                     match ex'^ in (_ = y) return (y = xq) with
                     | idpath => idpath
                     end in (_ = y)
                     return
                     (O
                        {q10 : Q (pr1 y) yq.1 &
                               sglue yq.2 @ (sglue q10)^ = r @ (sglue (pr2 y))^})
                   with
                   | idpath =>
                     to O {q10 : Q x0 yq.1 & sglue yq.2 @ (sglue q10)^ = r @ (sglue q01)^}
                        (yq.2;
                         concat_pV (sglue yq.2) @
                                   moveL_pV (sglue q01) 1 r (concat_1p (sglue q01) @ s))
                   end =
                  match
                    ey in (_ = y)
                    return
                    (O
                       {q10 : Q xq.1 (pr1 y) &
                              sglue (pr2 y) @ (sglue q10)^ = r @ (sglue xq.2)^})
                  with
                  | idpath =>
                    to O {q10 : Q xq.1 y1 & sglue q01 @ (sglue q10)^ = r @ (sglue xq.2)^}
                       (xq.2; whiskerR s (sglue xq.2)^)
                  end
                 ).
          clearbody xq yq. clear x1 q11 y0 q00.
          destruct ey, ex'; cbn.
          apply ap; apply ap.
          apply bar. }
      { refine (O_ind _ _).
        intros [q01 s].
        rewrite O_rec_beta; cbn.
        admit. }
      { admit. }
    Admitted.

    Definition iscontr_code (x0 : X) (y0 : Y) (q00 : Q x0 y0)
               (p : spushout) (r : spushl x0 = p)
      : Contr (code x0 y0 q00 p r).
    Proof.    
      srapply BuildContr.
      { destruct r.
        (* ... *)
        admit. }
      { admit. }
    Admitted.

    Definition gen_blakers_massey (x:X) (y:Y) (p : spushl x = spushr y)
      : IsConnected O (hfiber sglue p).
    Proof.
      (* ... *)
    Admitted.

  End GBM.
End BlakersMassey.
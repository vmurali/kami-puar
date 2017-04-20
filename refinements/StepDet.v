Require Import Bool List String Omega.
Require Import Lib.CommonTactics Lib.FMap Lib.Struct Lib.StringEq.
Require Import Kami.Syntax Kami.Semantics Kami.SemFacts Kami.Wf.

Set Implicit Arguments.

Set Asymmetric Patterns.

(* TODO: maybe to FMap.v? *)
Lemma elements_cons:
  forall {A} (k: string) (v: A) m l,
    (k, v) :: l = M.elements m ->
    exists pm,
      m = M.add k v pm /\ M.find k pm = None /\
      l = M.elements pm.
Proof.
Admitted.

Section NoCalls.
  Fixpoint actionNoCalls {retT} (a: ActionT typeUT retT) :=
    match a with
    | MCall name _ _ cont => false
    | Let_ _ ar cont => actionNoCalls (cont (getUT _))
    | ReadNondet k cont => actionNoCalls (cont (getUT _))
    | ReadReg reg k cont => actionNoCalls (cont (getUT _))
    | WriteReg reg _ e cont => actionNoCalls cont
    | IfElse ce _ ta fa cont =>
      (actionNoCalls ta) && (actionNoCalls fa) && (actionNoCalls (cont tt))
    | Assert_ ae cont => actionNoCalls cont
    | Return e => true
    end.

  Definition dmNoCalls (dm: DefMethT) :=
    actionNoCalls (projT2 (attrType dm) typeUT tt).

  Lemma actionNoCalls_SemAction:
    forall {retT} (aU: ActionT type retT) (aT: ActionT typeUT retT),
      ActionEquiv aU aT ->
      actionNoCalls aT = true ->
      forall o u cs ret,
        SemAction o aU u cs ret ->
        cs = M.empty _.
  Proof.
    induction 1; simpl; intros; try (inv H2; destruct_existT; eauto; fail).
    - inv H1; destruct_existT; eauto.
    - do 2 (apply andb_true_iff in H3; dest).
      inv H4; destruct_existT.
      + apply IHActionEquiv1 in HAction; auto; subst.
        eapply H2 in HSemAction; eauto.
      + apply IHActionEquiv2 in HAction; auto; subst.
        eapply H2 in HSemAction; eauto.
    - inv H1; destruct_existT; eauto.
    - inv H0; auto.
  Qed.

  Corollary dmNoCalls_Substep:
    forall f,
      MethEquiv type typeUT f ->
      dmNoCalls f = true ->
      forall o u mcs argV retV,
        SemAction o (projT2 (attrType f) type argV) u mcs retV ->
        mcs = M.empty _.
  Proof.
    intros; eapply actionNoCalls_SemAction; eauto.
  Qed.

End NoCalls.

Section OneDepth.
  Variable m : Modules.
  Hypotheses (Hequiv: ModEquiv type typeUT m)
             (Hdms: Forall (fun dm => dmNoCalls dm = true) (getDefsBodies m)).

  Section GivenOldRegs.
    Variable o : RegsT.

    (* Note that [SubstepMeths] doesn't need to collect labels 
     * since by an assumption there're no calls in methods! 
     *)
    Inductive SubstepMeths : list (string * {x : SignatureT & SignT x}) -> UpdatesT -> Prop :=
    | SmsNil: SubstepMeths nil (M.empty _)
    | SmsCons:
        forall pms pu,
          SubstepMeths pms pu ->
          forall mn mar u cs,
            Substep m o u (Meth (Some (mn :: mar)%struct)) cs ->
            M.Disj pu u ->
            SubstepMeths ((mn, mar) :: pms) (M.union pu u).

    Inductive StepDet : UpdatesT -> LabelT -> Prop :=
    | SbEmptyRule:
        StepDet (M.empty _) {| annot := Some None; defs := M.empty _; calls := M.empty _ |}
    | SbEmptyMeth:
        StepDet (M.empty _) {| annot := None; defs := M.empty _; calls := M.empty _ |}
    | SbRule:
        forall ru rcs rn,
          Substep m o ru (Rle (Some rn)) rcs ->
          forall mu,
            SubstepMeths (M.elements (M.restrict rcs (getDefs m))) mu ->
            M.Disj ru mu ->
            forall u cs,
              u = M.union ru mu ->
              cs = M.complement rcs (getDefs m) ->
              StepDet u {| annot := Some (Some rn);
                           defs := M.empty _;
                           calls := cs |}
    | SbMeth:
        forall mu mcs mn mar,
          (* mcs should be empty, but we don't care. *)
          Substep m o mu (Meth (Some (mn :: mar)%struct)) mcs ->
          In mn (getExtDefs m) ->
          forall ds,
            ds = [mn <- mar]%fmap ->
            StepDet mu {| annot := None;
                          defs := ds;
                          calls := mcs |}.

  End GivenOldRegs.

  Lemma substepMeths_implies_substepsInd:
      forall o mu meths,
        SubstepMeths o meths mu ->
        forall ms,
          M.KeysSubset ms (getDefs m) ->
          meths = M.elements ms ->
          SubstepsInd m o mu {| annot := None;
                                defs := ms;
                                calls := M.empty _ |}.
  Proof.
    induction 1; simpl; intros.
    - apply eq_sym, M.F.P.elements_Empty in H0.
      apply M.empty_canon in H0; subst.
      constructor.
    - assert (cs = M.empty _).
      { inv H0; inv Hsig.
        eapply dmNoCalls_Substep; eauto.
        { unfold ModEquiv in Hequiv; destruct Hequiv.
          eapply MethsEquiv_in in H4; eauto.
        }
        { eapply Forall_forall in Hdms; eauto. }
      }
      subst.
      apply elements_cons in H3; dest; subst.

      econstructor.
      + eapply IHSubstepMeths; try reflexivity.
        eapply M.KeysSubset_add_1; eauto.
      + eassumption.
      + unfold CanCombineUUL; cbn; repeat split; [mdisj|mdisj|findeq].
      + reflexivity.
      + reflexivity.
  Qed.

  Lemma stepDet_implies_step:
    forall o u l, StepDet o u l -> Step m o u l.
  Proof.
    intros; inv H; try (apply step_empty; auto).

    - assert (Hl: {| annot := Some (Some rn);
                     defs := M.empty _;
                     calls := M.complement rcs (getDefs m) |} =
                  hide {| annot := Some (Some rn);
                          defs := M.restrict rcs (getDefs m);
                          calls := rcs |}).
      { unfold hide; cbn; f_equal.
        { (* TODO: better to have a lemma in FMap.v *)
          M.ext y.
          rewrite M.subtractKV_find.
          rewrite M.restrict_find.
          destruct (in_dec M.F.P.F.eq_dec y (getDefs m)); auto.
          destruct (M.find y rcs); auto.
          destruct (signIsEq s s); auto.
          elim n; auto.
        }
        { (* TODO: better to have a lemma in FMap.v *)
          M.ext y.
          rewrite M.subtractKV_find, M.complement_find, M.restrict_find.
          destruct (in_dec M.F.P.F.eq_dec y (getDefs m)).
          { destruct (M.find y rcs); auto.
            destruct (signIsEq s s); auto.
            elim n; auto.
          }
          { destruct (M.find y rcs); auto. }
        }
      }
      rewrite Hl.

      apply step_consistent.
      constructor.
      + econstructor 2 with
        (u:= mu) (l:= {| annot := None;
                         defs := M.restrict rcs (getDefs m);
                         calls := M.empty _ |}); try eassumption.
        * eapply substepMeths_implies_substepsInd; eauto.
          (* TODO: better to have a lemma in FMap.v *)
          unfold M.KeysSubset; intros.
          apply M.F.P.F.in_find_iff in H.
          rewrite M.restrict_find in H.
          destruct (in_dec M.F.P.F.eq_dec k (getDefs m)); auto.
          elim H; auto.
        * unfold CanCombineUUL; cbn; auto.
        * apply M.union_comm; auto.
        * unfold mergeLabel; cbn.
          f_equal; meq.
      + rewrite <-Hl.
        unfold wellHidden; cbn; split.
        * apply M.KeysDisj_empty.
        * (* TODO: better to have a lemma in FMap.v *)
          unfold M.KeysDisj; intros.
          findeq.
          rewrite M.complement_find.
          destruct (in_dec _ k (getDefs m)); auto.
          elim n; auto.

    - inv H0; inv Hsig.
      eapply Forall_forall in Hdms; eauto.
      assert (Hf: MethEquiv type typeUT f).
      { unfold ModEquiv in Hequiv; destruct Hequiv.
        eapply MethsEquiv_in in H0; eauto.
      }
      pose proof (dmNoCalls_Substep Hf Hdms _ HAction); subst.
      match goal with
      | [ |- Step _ _ _ ?l ] => change l with (hide l) 
      end.
      apply step_consistent.
      constructor.
      + econstructor 2 with
        (su:= u) (sul:= Meth (Some (attrName f :: _)%struct)) (scs:= M.empty _).
        * constructor.
        * econstructor; eauto.
        * unfold CanCombineUUL; cbn; repeat split; auto.
          findeq.
        * reflexivity.
        * reflexivity.
      + unfold wellHidden; cbn; split.
        * unfold M.KeysDisj; intros.
          findeq.
          unfold getExtDefs in H1.
          apply filter_In in H1; dest.
          apply negb_true_iff in H1.
          apply eq_sym, string_in_dec_not_in in H1; elim H1; auto.
        * apply M.KeysDisj_empty.
  Qed.

  Theorem step_consistent_det:
    forall o u l, StepDet o u l <-> Step m o u l.
  Proof.
    intros; split.
    - apply stepDet_implies_step.
    - admit.
  Admitted.

End OneDepth.


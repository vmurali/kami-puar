Require Import Kami.
Require Import Lib.CommonTactics Lib.Indexer.
Require Import Kami.Decomposition Kami.ModuleBoundEx.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import Proc.AbstractIsa Proc.Fetch Proc.Decode Proc.Execute Proc.InOrderEightStage.

Set Implicit Arguments.
Open Scope string.

(** TODO: move to the general place *)
Require Import FunctionalExtensionality.

Section DropMeths.
  Variable dropMeths: list string.

  Definition dropMeths_vp (n: string) (v: (sigT SignT)): option (sigT SignT) :=
    if in_dec string_dec n dropMeths
    then None
    else Some v.

  Definition dropMeths_p (cs: MethsT) := M.complement cs dropMeths.

  Lemma dropMeths_vp_p:
    liftToMap1 dropMeths_vp = dropMeths_p.
  Proof.
    extensionality cs.
    M.ext x.
    unfold dropMeths_vp, dropMeths_p.
    rewrite SemFacts.liftToMap1_find.
    rewrite M.complement_find.
    change M.F.P.F.eq_dec with string_dec.
    destruct (in_dec string_dec x dropMeths); findeq.
  Qed.

End DropMeths.

(** TODO: merge into the Kami master branch. *)

Ltac kinv_constr_light :=
  repeat
    match goal with
    | |- exists _, _ /\ _ => eexists; split
    | |- Substep _ _ _ _ _ => econstructor
    | |- In _ _ => simpl; tauto
    | |- SemAction _ _ _ _ _ => econstructor
    | |- _ = _ => reflexivity
    end; kinv_red.

Ltac kinv_constr_light_false :=
  repeat
    match goal with
    | |- exists _, _ /\ _ => eexists; split
    | |- Substep _ _ _ _ _ => econstructor
    | |- In _ _ => simpl; tauto
    | |- SemAction _ (IfElse _ _ _ _) _ _ _ => eapply SemIfElseFalse
    | |- SemAction _ _ _ _ _ => econstructor
    | |- _ = _ => reflexivity
    end; kinv_red.

Ltac kinv_constr_light_unit :=
  match goal with
  | |- exists _, _ /\ _ => eexists; split
  | |- Substep _ _ _ _ _ => econstructor
  | |- In _ _ => simpl; tauto
  | |- SemAction _ _ _ _ _ => econstructor
  | |- _ = _ => reflexivity
  end.

Ltac meqReify_light :=
  simpl; apply M.elements_eq_leibniz; simpl; meqReify_eq_tac.

Ltac kinv_eq_light :=
  repeat (first [ meqReify_light | fin_func_eq | apply existT_eq | apply pair_eq ]);
  try reflexivity.

Ltac kmodular_ex :=
  try (unfold MethsT; rewrite <-SemFacts.idElementwiseId);
  apply traceRefines_modular_interacting with (vp:= (@idElementwise _));
  [kequiv|kequiv|kequiv|kequiv
   |kdisj_regs_ex O|kdisj_regs_ex O|kvr|kvr
   |kdisj_dms_ex O|kdisj_cms_ex O|kdisj_dms_ex O|kdisj_cms_ex O
   |kdisj_edms_cms_ex O|kdisj_ecms_dms_ex O|kinteracting| |].

Section Processor.
  Variables addrSize dataBytes rfIdx: nat.

  Variable decodeInst: DecodeT dataBytes rfIdx.
  Variable execInst: ExecT addrSize dataBytes rfIdx.

  Variables btbIndexSize btbTagSize bhtIndexSize bhtTrainSize: nat.
  Variables (getIndex: forall {ty}, fullType ty (SyntaxKind (Bit addrSize)) ->
                                    Expr ty (SyntaxKind (Bit btbIndexSize)))
            (getTag: forall {ty}, fullType ty (SyntaxKind (Bit addrSize)) ->
                                  Expr ty (SyntaxKind (Bit btbTagSize))).

  (** Fetch related *)
  Definition fetch := fetch addrSize dataBytes.
  Definition btb := btb getIndex getTag.
  Definition fetchNondet := fetchNondet addrSize dataBytes f2iName.
  Definition decRedir := decRedir addrSize.
  Definition exeRedir := exeRedir addrSize.
  Definition f2i := f2i addrSize dataBytes.

  (** IMem related *)
  Definition iMem := iMem addrSize dataBytes.
  Definition i2d := i2d addrSize dataBytes.

  (** Decode related *)
  Definition decode := decode addrSize decodeInst.
  Definition bht := bht addrSize bhtIndexSize.
  Definition bhtTrain := bhtTrain addrSize.
  Definition bhtTrainQ := bhtTrainQ addrSize bhtTrainSize.
  Definition bhtFrontEnd := bhtFrontEnd addrSize dataBytes rfIdx.
  Definition decodeNondet := decodeNondet addrSize i2dName d2rName decodeInst.
  Definition d2r := d2r addrSize dataBytes rfIdx.

  (** RegRead related *)
  Definition regRead := regRead addrSize dataBytes rfIdx.
  Definition rf := rf dataBytes rfIdx.
  Definition bypass := bypass dataBytes rfIdx.
  Definition r2e := r2e addrSize dataBytes rfIdx.

  (** Execute related *)
  Definition execute := execute execInst.
  Definition executeNondet := executeNondet r2eName e2mName execInst.
  Definition e2m := e2m addrSize dataBytes rfIdx.

  (** Mem related *)
  Definition mem := mem addrSize dataBytes rfIdx.
  Definition m2d := m2d addrSize dataBytes rfIdx.

  (** DMem related *)
  Definition dMem := dMem addrSize dataBytes rfIdx.
  Definition d2w := d2w addrSize dataBytes rfIdx.

  (** Writeback related *)
  Definition writeback := writeback addrSize dataBytes rfIdx.

  Definition inOrderEight :=
    inOrderEight decodeInst execInst bhtIndexSize bhtTrainSize getIndex getTag.

  Definition inOrderEight0 :=
    ((fetch ++ btb)
       ++ (decode ++ bht ++ bhtTrain ++ bhtTrainQ ++ bhtFrontEnd ++ execute)
       ++ (decRedir ++ exeRedir ++ exeEpoch ++ f2i ++
                    iMem ++ i2d ++ d2r ++
                    regRead ++ rf ++ bypass ++ r2e ++ e2m ++
                    mem ++ m2d ++
                    dMem ++ d2w ++
                    writeback))%kami.

  Definition inOrderEight1 :=
    (fetchNondet
       ++ (decodeNondet ++ executeNondet)
       ++ (decRedir ++ exeRedir ++ exeEpoch ++ f2i ++
                    iMem ++ i2d ++ d2r ++
                    regRead ++ rf ++ bypass ++ r2e ++ e2m ++
                    mem ++ m2d ++
                    dMem ++ d2w ++
                    writeback))%kami.

  Section Refinement0.

    Theorem inOrderEight_inOrderEight0: inOrderEight <<== inOrderEight0.
    Proof.
      (* ksimilar; equivList_app_tac. *)
    Admitted.

  End Refinement0.
          
  Section Refinement1.

    Local Definition dropRegsF : list string :=
      ["btbValid"; "btbTags"; "btbTargets"].
    Local Definition dropRegsD : list string :=
      ["full.bhtTrain"; "empty.bhtTrain";
         "deqP.bhtTrain"; "enqP.bhtTrain"; "elt.bhtTrain";
           "satCnt"].

    Local Definition thetaF (s: RegsT) : RegsT := M.complement s dropRegsF.
    Local Definition thetaD (s: RegsT) : RegsT := M.complement s dropRegsD.

    Local Definition dropMethsF : list string :=
      ["btbUpdate"; "btbPredPc"].
    Local Definition dropMethsD : list string :=
      ["firstElt.bhtTrain"; "deq.bhtTrain"; "enq.bhtTrain";
         "update"; "predTaken"; "bhtPredPc"].

    Local Definition pF := dropMeths_vp dropMethsF.
    Local Definition pD := dropMeths_vp dropMethsD.

    Local Definition dropRulesD : list string :=
      ["trainBht"].

    Local Definition ruleMapF (o: RegsT) (n: string) : option string := Some n.
    Local Definition ruleMapD (o: RegsT) (n: string) : option string :=
      if in_dec string_dec n dropRulesD then None else Some n.

    Ltac equiv_label_map :=
      repeat
        match goal with
        | [ |- EquivalentLabelMapElem _ _ _] =>
          unfold EquivalentLabelMapElem;
          let H := fresh "H" in
          intros ? H ?; vm_compute in H
        | [H: _ \/ _ |- _] => destruct H; subst
        | [H: False |- _] => inversion H
        end; try reflexivity.

    Ltac kdrop p t r :=
      apply traceRefines_labelMap_weakening with (vp:= p); [kequiv| |equiv_label_map];
      apply decompositionDrop with (theta:= t) (ruleMap:= r);
      [kequiv
      |vm_compute; tauto|vm_compute; tauto
      | |meqReify|meqReify
      | | | |].

    Theorem inOrderEight0_inOrderEight1: inOrderEight0 <<== inOrderEight1.
    Proof.
      (* kmodular_ex. *)
      
      (* - (** BTB drop *) *)
      (*   kdrop pF thetaF ruleMapF. *)
      (*   + intros. *)
      (*     unfold pF. *)
      (*     pose proof (dropMeths_vp_p dropMethsF); rewrite H0. *)
      (*     apply M.complement_Disj; auto. *)
      (*   + intros; apply M.complement_union. *)
      (*   + intros; apply M.complement_Disj; auto. *)
      (*   + intros. *)
      (*     kinvert. *)
      (*     * kinv_action_dest. *)
      (*       kinv_red. *)
      (*       kinv_constr_light; kinv_eq_light. *)
      (*       -- unfold thetaF; rewrite M.complement_find; simpl; auto. *)
      (*       -- unfold thetaF; rewrite M.complement_find; simpl; auto. *)
      (*       -- unfold thetaF; rewrite M.complement_find; simpl; auto. *)
      (*     * kinv_action_dest. *)
      (*       kinv_red. *)
      (*       kinv_constr_light; kinv_eq_light; kinv_finish. *)
      (*       -- unfold thetaF; rewrite M.complement_find; simpl; auto. *)
      (*       -- unfold thetaF; rewrite M.complement_find; simpl; auto. *)
      (*     * kinv_action_dest. *)
      (*       kinv_red. *)
      (*       kinv_constr_light; kinv_eq_light; kinv_finish. *)
      (*       unfold thetaF; rewrite M.complement_find; simpl; auto. *)
      (*   + intros. *)
      (*     kinvert. *)
      (*     * simpl; kinv_action_dest; econstructor. *)
      (*     * simpl; kinv_action_dest; econstructor. *)

      (* - kmodular_ex; [|krefl]. *)

      (*   (** BHT drop *) *)
      (*   kdrop pD thetaD ruleMapD. *)
      (*   + intros. *)
      (*     unfold pD. *)
      (*     pose proof (dropMeths_vp_p dropMethsD); rewrite H0. *)
      (*     apply M.complement_Disj; auto. *)
      (*   + intros; apply M.complement_union. *)
      (*   + intros; apply M.complement_Disj; auto. *)
      (*   + intros. *)
      (*     kinvert. *)
      (*     * kinv_action_dest. *)
      (*       kinv_red. *)
      (*       kinv_constr_light; kinv_eq_light; kinv_finish. *)
      (*       unfold thetaD; rewrite M.complement_find; simpl; auto. *)
      (*     * kinv_action_dest. *)
      (*       -- kinv_red. *)
      (*          kinv_constr_light; kinv_eq_light. *)
      (*          ++ unfold thetaD; rewrite M.complement_find; simpl; auto. *)
      (*          ++ simpl. *)
      (*             destruct (bool_dec _ _); auto. *)
      (*             destruct (bool_dec _ _); auto. *)
      (*          ++ simpl; destruct (weq _ WO~0~0~0~0); auto. *)
      (*          ++ mdisj. *)
      (*          ++ mdisj. *)
      (*          ++ simpl. *)
      (*             rewrite <-H4, <-H5. *)
      (*             reflexivity. *)
      (*       -- kinv_red. *)
      (*          kinv_constr_light_false; kinv_eq_light. *)
      (*          ++ unfold thetaD; rewrite M.complement_find; simpl; eauto. *)
      (*          ++ simpl. *)
      (*             destruct (bool_dec _ _); auto. *)
      (*             destruct (bool_dec _ _); auto. *)
      (*          ++ simpl; destruct (weq _ WO~0~0~0~0); auto. *)
      (*          ++ mdisj. *)
      (*          ++ mdisj. *)
      (*          ++ simpl. *)
      (*             apply eq_sym, Heqic. *)
      (*     * simpl; kinv_action_dest; econstructor. *)
      (*     * kinv_action_dest. *)
      (*       kinv_red. *)
      (*       kinv_constr_light; kinv_eq_light; kinv_finish. *)
      (*       destruct (bool_dec _ _); auto. *)
      (*     * kinv_action_dest. *)
      (*       -- kinv_red. *)
      (*          kinv_constr_light; kinv_eq_light. *)
      (*          ++ simpl; destruct (bool_dec _ _); auto. *)
      (*          ++ mdisj. *)
      (*          ++ mdisj. *)
      (*          ++ simpl; auto. *)
      (*       -- kinv_red. *)
      (*          kinv_constr_light_false; kinv_eq_light. *)
      (*          ++ simpl; destruct (bool_dec _ _); auto. *)
      (*          ++ mdisj. *)
      (*          ++ mdisj. *)
      (*          ++ simpl; auto. *)
      (*   + intros. *)
      (*     kinvert. *)
      (*     * simpl; kinv_action_dest; econstructor. *)
      (*     * simpl; kinv_action_dest; econstructor. *)
      (*     * simpl; kinv_action_dest; econstructor. *)
      (*     * simpl; kinv_action_dest; econstructor. *)
      (*     * simpl; kinv_action_dest; econstructor. *)
    Admitted.
    
  End Refinement1.
  
End Processor.

Hint Unfold fetch btb fetchNondet decRedir exeRedir f2i
     iMem i2d decode bht bhtTrain bhtTrainQ bhtFrontEnd
     decodeNondet d2r regRead rf bypass r2e
     execute executeNondet e2m
     mem m2d dMem d2w writeback
     inOrderEight inOrderEight0 inOrderEight1 : ModuleDefs.


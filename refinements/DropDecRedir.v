Require Import Kami.
Require Import Lib.CommonTactics Lib.Indexer.
Require Import Kami.Decomposition Kami.ModuleBoundEx.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import Proc.AbstractIsa Proc.Fetch Proc.Decode Proc.Execute Proc.InOrderEightStage.
Require Import DropBranchPredictors.

Set Implicit Arguments.
Open Scope string.

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
  Definition fetchNondet := fetchNondet addrSize dataBytes.
  Definition fetchNondetD := fetchNondetD addrSize dataBytes f2iName.
  Definition decRedir := decRedir addrSize.
  Definition exeRedir := exeRedir addrSize.
  Definition f2i := f2i addrSize dataBytes.

  (** IMem related *)
  Definition iMem := iMem addrSize dataBytes.
  Definition i2d := i2d addrSize dataBytes.

  (** Decode related *)
  Definition decodeNondet := decodeNondet addrSize decodeInst.
  Definition decodeNondetD := decodeNondetD addrSize i2dName d2rName decodeInst.
  Definition d2r := d2r addrSize dataBytes rfIdx.

  (** RegRead related *)
  Definition regRead := regRead addrSize dataBytes rfIdx.
  Definition rf := rf dataBytes rfIdx.
  Definition bypass := bypass dataBytes rfIdx.
  Definition r2e := r2e addrSize dataBytes rfIdx.

  (** Execute related *)
  Definition executeNondet := executeNondet execInst.
  Definition e2m := e2m addrSize dataBytes rfIdx.

  (** Mem related *)
  Definition mem := mem addrSize dataBytes rfIdx.
  Definition m2d := m2d addrSize dataBytes rfIdx.

  (** DMem related *)
  Definition dMem := dMem addrSize dataBytes rfIdx.
  Definition d2w := d2w addrSize dataBytes rfIdx.

  (** Writeback related *)
  Definition writeback := writeback addrSize dataBytes rfIdx.

  Definition inOrderEight1 := inOrderEight1 decodeInst execInst.

  Definition inOrderEight2 :=
    ((fetchNondet ++ decRedir ++ decEpoch ++ decodeNondet)
       ++ (f2i ++ iMem ++ i2d ++
               d2r ++ regRead ++ rf ++ bypass ++ r2e ++
               executeNondet ++ exeRedir ++ exeEpoch ++ e2m ++
               mem ++ m2d ++
               dMem ++ d2w ++
               writeback))%kami.

  Definition inOrderEight3 :=
    ((fetchNondetD ++ decodeNondetD)
       ++ (f2i ++ iMem ++ i2d ++
               d2r ++ regRead ++ rf ++ bypass ++ r2e ++
               executeNondet ++ exeRedir ++ exeEpoch ++ e2m ++
               mem ++ m2d ++
               dMem ++ d2w ++
               writeback))%kami.

  Section Refinement2.

    Theorem inOrderEight1_inOrderEight2: inOrderEight1 <<== inOrderEight2.
    Proof.
      (* ksimilar; equivList_app_tac. *)
    Admitted.

  End Refinement2.
  
  Section Refinement3.

    Local Definition dropRegs : list string :=
      ["dec"; "decEpoch"].

    Local Definition theta (s: RegsT) : RegsT := M.complement s dropRegs.

    Local Definition dropMeths : list string :=
      ["redirGet.dec"; "redirSetInvalid.dec"; "redirSetValid.dec";
         "decGetEpoch1"; "decGetEpoch2"; "decToggleEpoch"].

    Local Definition p := dropMeths_vp dropMeths.

    Local Definition ruleMap (o: RegsT) (n: string) : option string := Some n.

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

    Theorem inOrderEight2_inOrderEight3: inOrderEight2 <<== inOrderEight3.
    Proof.
      (* kmodular_ex; [|krefl]. *)

      (* kdrop p theta ruleMap. *)
      (* - intros. *)
      (*   unfold p. *)
      (*   pose proof (dropMeths_vp_p dropMeths); rewrite H0. *)
      (*   apply M.complement_Disj; auto. *)
      (* - intros; apply M.complement_union. *)
      (* - intros; apply M.complement_Disj; auto. *)
      (* - intros. *)
      (*   kinvert. *)
      (*   + kinv_action_dest. *)
      (*     kinv_red. *)
      (*     kinv_constr_light; kinv_eq_light. *)
      (*     unfold theta; rewrite M.complement_find; simpl; auto. *)
      (*   + kinv_action_dest. *)
      (*     kinv_red. *)
      (*     kinv_constr_light; kinv_eq_light. *)
      (*     simpl; auto. *)
      (*   + kinv_action_dest. *)
      (*     kinv_red. *)
      (*     kinv_constr_light; kinv_eq_light; kinv_finish. *)
      (*   + kinv_action_dest. *)
      (*     kinv_red. *)
      (*     kinv_constr_light; kinv_eq_light; kinv_finish. *)
      (*   + kinv_action_dest. *)
      (*     * kinv_red. *)
      (*       kinv_constr_light; kinv_eq_light. *)
      (*       -- simpl. *)
      (*          destruct (bool_dec _ _); auto. *)
      (*       -- simpl; destruct (weq _ WO~0~0~0~0); auto. *)
      (*       -- exact true. *)
      (*     * kinv_red. *)
      (*       kinv_constr_light_false; kinv_eq_light. *)
      (*       -- simpl. *)
      (*          destruct (bool_dec _ _); auto. *)
      (*       -- simpl; destruct (weq _ WO~0~0~0~0); auto. *)
      (*       -- exact true. *)
      (* - intros. *)
      (*   kinvert. *)
      (*   + simpl; kinv_action_dest; econstructor. *)
      (*   + simpl; kinv_action_dest; econstructor. *)
      (*   + simpl; kinv_action_dest; econstructor. *)
      (*   + simpl; kinv_action_dest; econstructor. *)
      (*   + simpl; kinv_action_dest; econstructor. *)
      (*   + simpl; kinv_action_dest; econstructor. *)
    Admitted.

  End Refinement3.
  
End Processor.


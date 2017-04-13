Require Import Kami.
Require Import Lib.CommonTactics Lib.Indexer.
Require Import Kami.Decomposition.
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
  Definition fetchNondet := fetchNondet addrSize dataBytes f2iName.
  Definition decRedir := decRedir addrSize.
  Definition exeRedir := exeRedir addrSize.
  Definition f2i := f2i addrSize dataBytes.

  (** IMem related *)
  Definition iMem := iMem addrSize dataBytes.
  Definition i2d := i2d addrSize dataBytes.

  (** Decode related *)
  Definition decodeNondet := decodeNondet addrSize i2dName d2rName decodeInst.
  Definition d2r := d2r addrSize dataBytes rfIdx.

  (** RegRead related *)
  Definition regRead := regRead addrSize dataBytes rfIdx.
  Definition rf := rf dataBytes rfIdx.
  Definition bypass := bypass dataBytes rfIdx.
  Definition r2e := r2e addrSize dataBytes rfIdx.

  (** Execute related *)
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

  (* inOrderEight :=
     (fetch ++ btb ++ decRedir ++ exeRedir ++ decEpoch ++ exeEpoch ++ f2i ++
     iMem ++ i2d ++
     decode ++ bht ++ bhtTrain ++ bhtTrainQ ++ d2r ++
     regRead ++ rf ++ bypass ++ r2e ++
     execute ++ e2m ++
     mem ++ m2d ++
     dMem ++ d2w ++
     writeback)%kami.
   *)
  Definition inOrderEight :=
    inOrderEight decodeInst execInst bhtIndexSize bhtTrainSize getIndex getTag.

  Definition inOrderEight0 :=
    (fetchNondet ++ decRedir ++ exeRedir ++ decEpoch ++ exeEpoch ++ f2i ++
                 iMem ++ i2d ++
                 decodeNondet ++ d2r ++
                 regRead ++ rf ++ bypass ++ r2e ++
                 executeNondet ++ e2m ++
                 mem ++ m2d ++
                 dMem ++ d2w ++
                 writeback)%kami.

  Section Refinement.

    (* Eval compute in (Struct.namesOf (getRegInits inOrderEight)). *)
    (* Eval compute in (Struct.namesOf (getRegInits inOrderEight0)). *)

    Local Definition dropRegs : list string :=
      ["full.bhtTrain"; "empty.bhtTrain"; "deqP.bhtTrain"; "enqP.bhtTrain"; "elt.bhtTrain";
         "satCnt"; "btbValid"; "btbTags"; "btbTargets"].

    Local Definition theta (s: RegsT) : RegsT := M.complement s dropRegs.

    (* Eval compute in (getDefs inOrderEight). *)
    (* Eval compute in (getDefs inOrderEight0). *)

    Local Definition dropMeths : list string :=
      ["firstElt.bhtTrain"; "deq.bhtTrain"; "enq.bhtTrain"; "update"; "predTaken";
         "btbUpdate"; "btbPredPc"].
    (* pose (getDefs inOrderEight) as pdefs; compute in pdefs. *)
    (* pose (getDefs inOrderEight0) as ndefs; compute in ndefs. *)
    (* pose (fold_left (fun nl e => *)
    (*                    if in_dec string_dec e ndefs then nl else e :: nl) pdefs nil) as ddefs. *)
    (* compute in ddefs. *)

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

    Theorem inOrderEight_inOrderEight0: inOrderEight <<== inOrderEight0.
    Proof.
      apply traceRefines_labelMap_weakening with (vp:= p);
        [kequiv| |equiv_label_map].

      apply decompositionDrop with (theta:= theta) (ruleMap:= ruleMap).
      - kequiv.
      - vm_compute; tauto.
      - vm_compute; tauto.
      - intros.
        unfold p.
        pose proof (dropMeths_vp_p dropMeths); rewrite H0.
        apply M.complement_Disj; auto.
      - meqReify.
      - meqReify.
      - intros; apply M.complement_union.
      - intros; apply M.complement_Disj; auto.
      - (** TODO: just need one trivial invariant: a state always has register 
         * values initially defined. *)
        admit.

        (* With the above invariant, below should work. *)
        (* intros. *)
        (* kinvert. *)
        (* + kinv_action_dest; *)
        (*     kinv_custom idtac; *)
        (*     kinv_regmap_red; *)
        (*     kinv_constr; *)
        (*     kinv_eq. *)
      - (** TODO: just need one trivial invariant: a state always has register 
         * values initially defined. *)

        (* Confirmed kinv_magic works fast enough for drop cases *)
        admit.
    Admitted.

  End Refinement.
  
End Processor.


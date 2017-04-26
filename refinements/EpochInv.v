Require Import Kami.
Require Import Lib.CommonTactics Lib.Indexer Lib.VectorFacts.
Require Import Kami.Decomposition Kami.ModuleBoundEx.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import Proc.AbstractIsa Proc.Fetch Proc.Decode Proc.RegRead Proc.Execute
        Proc.InOrderEightStage.
Require Import DropBranchPredictors Fidre.

Require Import StepDet. (* TODO: should move to Kami *)

Set Implicit Arguments.
Open Scope string.

(** TODO: move to SemFacts.v *)
Section StepToInvariant.
  Variable m: Modules.
  Variable P: RegsT -> Prop.
  Hypothesis HinitP: P (initRegs (getRegInits m)).

  Hypothesis HstepP:
    forall o u l,
      P o -> Step m o u l -> P (M.union u o).

  Lemma multistep_P:
    forall init n ll,
      init = initRegs (getRegInits m) ->
      Multistep m init n ll ->
      P n.
  Proof.
    induction 2; [repeat subst; auto|].
    specialize (IHMultistep H).
    eauto.
  Qed.

  Lemma stepInv:
    forall o, reachable o m -> P o.
  Proof.
    intros; inv H; inv H0.
    eapply multistep_P; eauto.
  Qed.
      
End StepToInvariant.

Section Processor.
  Variables addrSize dataBytes rfIdx: nat.

  Variable decodeInst: DecodeT dataBytes rfIdx.
  Variable execInst: ExecT addrSize dataBytes rfIdx.

  (** Fetch related *)
  Definition fetchNondet := fetchNondet addrSize dataBytes.
  Definition fetchNondetNR := fetchNondetNR addrSize dataBytes f2iName.
  Definition decRedir := decRedir addrSize.
  Definition exeRedir := exeRedir addrSize.
  Definition f2i := f2i addrSize dataBytes.

  (** IMem related *)
  Definition iMem := iMem addrSize dataBytes.
  Definition i2d := i2d addrSize dataBytes.

  (** Decode related *)
  Definition decodeNondet := decodeNondet addrSize decodeInst.
  Definition decodeNondetNR := decodeNondetNR addrSize i2dName d2rName decodeInst.
  Definition d2r := d2r addrSize dataBytes rfIdx.

  (** RegRead related *)
  Definition regRead := regRead addrSize dataBytes rfIdx.
  Definition rf := rf dataBytes rfIdx.
  Definition bypass := bypass dataBytes rfIdx.
  Definition r2e := r2e addrSize dataBytes rfIdx.

  (** Execute related *)
  Definition executeNondet := executeNondet execInst.
  Definition executeNondetNR := executeNondetNR r2eName e2mName execInst.

  Definition fidreComb := fidreComb decodeInst execInst.

  Record epoch_invariant (o: RegsT) : Prop :=
    { fetchEpochDv : fullType type (SyntaxKind Bool);
      Hfed: M.find "fetchEpochD" o = Some (existT _ _ fetchEpochDv);
      fetchEpochEv : fullType type (SyntaxKind Bool);
      Hfee: M.find "fetchEpochE" o = Some (existT _ _ fetchEpochEv);
      decEpochv : fullType type (SyntaxKind Bool);
      Hde: M.find "decEpoch" o = Some (existT _ _ decEpochv);
      exeEpochv : fullType type (SyntaxKind Bool);
      Hee: M.find "exeEpoch" o = Some (existT _ _ exeEpochv);

      decRedirv : fullType type (SyntaxKind (RedirectK addrSize));
      Hdr : M.find "dec" o = Some (existT _ _ decRedirv);
      exeRedirv : fullType type (SyntaxKind (RedirectK addrSize));
      Her : M.find "exe" o = Some (existT _ _ exeRedirv);

      HdeSpec1: fetchEpochDv = decEpochv -> decRedirv Fin.F1 (* isValid *) = false;
      HdeSpec2: decRedirv Fin.F1 = false -> fetchEpochDv = decEpochv;

      HeeSpec1: fetchEpochEv = exeEpochv -> exeRedirv Fin.F1 = false;
      HeeSpec2: exeRedirv Fin.F1 = false -> fetchEpochEv = exeEpochv }.

  Local Notation "'_STRUCT_'" := (fun i : Fin.t _ => _).
  Local Notation "'_STRUCT_SIG_'" := (forall i : Fin.t _, _).

  Lemma fidreComb_epoch_invariant_ok:
    forall o, reachable o fidreComb -> epoch_invariant o.
  Proof.
    intros; apply stepInv with (m:= fidreComb); auto;
      [econstructor;
       try (findReify; (reflexivity || eassumption); fail);
       auto|].

    clear H o; intros.
    apply step_implies_stepDet in H0;
      [|kequiv|repeat (constructor || reflexivity)|reflexivity].
    inv H0; simpl; try mred.

    kinvert.

    - (* doFetch *)
      kinv_action_dest.
      kinv_red; kregmap_red.
      kinvert_det; kinv_action_dest.

      destruct H.
      kinv_red; kregmap_red; kinv_red.
      econstructor;
        try (findReify; try (reflexivity || eassumption); fail);
        try assumption.

    - (* redirectExe *)
      kinv_action_dest.
      kinv_red; kregmap_red.
      kinvert_det; kinv_action_dest.

      destruct H.
      kinv_red; kregmap_red; kinv_red.
      econstructor;
        try (findReify; try (reflexivity || eassumption); fail);
        try assumption.

      + destruct (x5 Fin.F1); auto.
      + inv H1.
        destruct (x6 Fin.F1); auto.
        destruct x0, decEpochv; auto.
        specialize (HdeSpec1 eq_refl); discriminate.
      + intros; reflexivity.
      + inv H6; rewrite H4 in *.
        destruct x2, exeEpochv; auto.
        specialize (HeeSpec1 eq_refl); discriminate.
        
    - (* redirectDec *)
      kinv_action_dest.
      kinv_red; kregmap_red.
      kinvert_det; kinv_action_dest.

      destruct H.
      kinv_red; kregmap_red; kinv_red.
      econstructor;
        try (findReify; try (reflexivity || eassumption); fail);
        try assumption.

      + intros; reflexivity.
      + inv H1; rewrite H6 in *.
        destruct x3, decEpochv; auto.
        specialize (HdeSpec1 eq_refl); discriminate.
        
    - (* doIMem *)
      kinv_action_dest.
      kinv_red; kregmap_red.
      kinvert_det; kinv_action_dest.

      destruct H.
      kinv_red; kregmap_red; kinv_red.
      econstructor;
        try (findReify; try (reflexivity || eassumption); fail);
        try assumption.
      
    - (* killDecode *)
      kinv_action_dest.
      kinv_red; kregmap_red.
      kinvert_det; kinv_action_dest.

      destruct H.
      kinv_red; kregmap_red; kinv_red.
      econstructor;
        try (findReify; try (reflexivity || eassumption); fail);
        try assumption.
      
    - (* doDecode *)
      kinv_action_dest;
        kinv_red; kregmap_red;
          kinvert_det; kinv_action_dest.
      
      + destruct H.
        kinv_red; kregmap_red; kinv_red.
        econstructor;
          try (findReify; try (reflexivity || eassumption); fail);
          try assumption.
        * specialize (HdeSpec2 e).
          subst; intros.
          exfalso; eapply no_fixpoint_negb; eauto.
        * intros; discriminate.

      + destruct H.
        kinv_red; kregmap_red; kinv_red.
        econstructor;
          try (findReify; try (reflexivity || eassumption); fail);
          try assumption.

    - (* doRegRead *)
      kinv_action_dest;
        kinv_red; kregmap_red;
          kinvert_det; kinv_action_dest;
            abstract (destruct H;
                      kinv_red; kregmap_red; kinv_red;
                      econstructor;
                      try (findReify; try (reflexivity || eassumption); fail);
                      try assumption).
      
    - (* killExecute *)
      kinv_action_dest.
      kinv_red; kregmap_red.
      kinvert_det; kinv_action_dest.

      destruct H.
      kinv_red; kregmap_red; kinv_red.
      econstructor;
        try (findReify; try (reflexivity || eassumption); fail);
        try assumption.

    - (* doExecute *)
      kinv_action_dest;
        kinv_red; kregmap_red;
          kinvert_det; kinv_action_dest.
      
      + destruct H.
        kinv_red; kregmap_red; kinv_red.
        econstructor;
          try (findReify; try (reflexivity || eassumption); fail);
          try assumption.
        * specialize (HeeSpec2 e).
          subst; intros.
          exfalso; eapply no_fixpoint_negb; eauto.
        * intros; discriminate.

      + destruct H.
        kinv_red; kregmap_red; kinv_red.
        econstructor;
          try (findReify; try (reflexivity || eassumption); fail);
          try assumption.
  Qed.
  
End Processor.


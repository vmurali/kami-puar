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

  (** Some definitions for defining invariants *)
  Definition F2I := F2I addrSize dataBytes.
  Definition I2D := I2D addrSize dataBytes.
  Definition D2R := D2R addrSize dataBytes rfIdx.
  Definition R2E := R2E addrSize dataBytes rfIdx.

  Definition f2iValid (decEpoch exeEpoch: bool) (e: type (Struct F2I)) :=
    eqb (e Fin.F1 (Fin.FS (Fin.FS Fin.F1))) decEpoch &&
        eqb (e Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) exeEpoch.

  Definition i2dValid (decEpoch exeEpoch: bool) (e: type (Struct I2D)) :=
    eqb (e Fin.F1 (Fin.FS (Fin.FS Fin.F1))) decEpoch &&
        eqb (e Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) exeEpoch.

  Definition d2rValid (exeEpoch: bool) (e: type (Struct D2R)) :=
    eqb (e (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) exeEpoch.

  Definition r2eValid (exeEpoch: bool) (e: type (Struct R2E)) :=
    eqb (e (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))) exeEpoch.

  Record EpochPc := { pPc : word addrSize;
                      pPredPc : word addrSize;
                      pDecEpoch : option bool;
                      pExeEpoch : bool }.

  Definition f2iToEpochPc (f2ie: type (Struct F2I)) :=
    {| pPc := f2ie Fin.F1 Fin.F1;
       pPredPc := f2ie Fin.F1 (Fin.FS Fin.F1);
       pDecEpoch := Some (f2ie Fin.F1 (Fin.FS (Fin.FS Fin.F1)));
       pExeEpoch := f2ie Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1))) |}.

  Definition i2dToEpochPc (i2de: type (Struct I2D)) :=
    {| pPc := i2de Fin.F1 Fin.F1;
       pPredPc := i2de Fin.F1 (Fin.FS Fin.F1);
       pDecEpoch := Some (i2de Fin.F1 (Fin.FS (Fin.FS Fin.F1)));
       pExeEpoch := i2de Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1))) |}.

  Definition d2rToEpochPc (d2re: type (Struct D2R)) :=
    {| pPc := d2re Fin.F1;
       pPredPc := d2re (Fin.FS Fin.F1);
       pDecEpoch := None;
       pExeEpoch := d2re (Fin.FS (Fin.FS (Fin.FS Fin.F1))) |}.

  Definition r2eToEpochPc (r2ee: type (Struct R2E)) :=
    {| pPc := r2ee Fin.F1;
       pPredPc := r2ee (Fin.FS Fin.F1);
       pDecEpoch := None;
       pExeEpoch := r2ee (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))) |}.

  (* NOTE: head is the oldest *)
  Definition epochPcFidre
             (f2iv: list (type (Struct F2I))) (i2dv: list (type (Struct I2D)))
             (d2rv: list (type (Struct D2R))) (r2ev: list (type (Struct R2E))) :=
    ((map r2eToEpochPc r2ev)
       ++ (map d2rToEpochPc d2rv)
       ++ (map i2dToEpochPc i2dv)
       ++ (map f2iToEpochPc f2iv))%list.

  Definition epochPcDre
             (d2rv: list (type (Struct D2R))) (r2ev: list (type (Struct R2E))) :=
    ((map r2eToEpochPc r2ev) ++ (map d2rToEpochPc d2rv))%list.

  Definition getOldest
             (f2i: list (type (Struct F2I))) (i2d: list (type (Struct I2D)))
             (d2r: list (type (Struct D2R))) (r2e: list (type (Struct R2E))) :=
    match epochPcFidre f2i i2d d2r r2e with
    | nil => None
    | hd :: _ => Some hd
    end.

  (** [pcChainFromPc] and [pcChainFromDec] describe invariants
   * when there are no redirections, saying that pc/predPc pairs generate
   * a chain (started from either [pc] or [decRedir]) throughout the fifos.
   *)
  Definition decEpochMatches (decEpoch: bool) (pDecEpoch: option bool) :=
    match pDecEpoch with
    | Some pde => eqb pde decEpoch
    | None => true
    end.

  (* NOTE: head should be the youngest! *)
  Fixpoint pcChain (pcv: fullType type (SyntaxKind (Bit addrSize)))
           (eps: list EpochPc) :=
    match eps with
    | nil => True
    | ep :: eps' => pcv = pPredPc ep /\ pcChain (pPc ep) eps'
    end.

  Lemma pcChain_app:
    forall (eps1 eps2: list EpochPc) pcv,
      pcChain pcv (eps1 ++ eps2) ->
      pcChain pcv eps1 /\ pcChain (match List.rev eps1 with
                                   | nil => pcv
                                   | ep :: _ => pPc ep
                                   end) eps2.
  Proof.
    induction eps1; simpl; intros; eauto.
    dest; subst.
    specialize (IHeps1 _ _ H0); dest.
    repeat split; auto.
    remember (List.rev eps1) as reps1; destruct reps1;
      simpl in *; auto.
  Qed.

  Definition pcChainFromPc (pcv: fullType type (SyntaxKind (Bit addrSize)))
             (decEpochv exeEpochv: fullType type (SyntaxKind Bool))
             (f2iv: list (type (Struct F2I))) (i2dv: list (type (Struct I2D)))
             (d2rv: list (type (Struct D2R))) (r2ev: list (type (Struct R2E))) :=
    pcChain
      pcv (List.rev (List.filter (fun ep => (decEpochMatches decEpochv (pDecEpoch ep))
                                              && (eqb (pExeEpoch ep) exeEpochv))
                                 (epochPcFidre f2iv i2dv d2rv r2ev))).

  Definition pcChainFromDec (pcv: fullType type (SyntaxKind (Bit addrSize)))
             (exeEpochv: fullType type (SyntaxKind Bool))
             (d2rv: list (type (Struct D2R))) (r2ev: list (type (Struct R2E))) :=
    pcChain
      pcv (List.rev (List.filter (fun ep => eqb (pExeEpoch ep) exeEpochv)
                                 (epochPcDre d2rv r2ev))).

  Lemma pcChainFromPc_f2i_enq:
    forall pcv pcv' decEpochv exeEpochv f2iv (f2ie: type (Struct F2I)) i2dv d2rv r2ev,
      pcChainFromPc pcv decEpochv exeEpochv f2iv i2dv d2rv r2ev ->
      f2iValid decEpochv exeEpochv f2ie = true ->
      pcv = f2ie Fin.F1 Fin.F1 ->
      pcv' = f2ie Fin.F1 (Fin.FS Fin.F1) ->
      pcChainFromPc pcv' decEpochv exeEpochv (f2iv ++ [f2ie]) i2dv d2rv r2ev.
  Proof.
    unfold pcChainFromPc, epochPcFidre; intros.
    repeat (rewrite filter_app || rewrite rev_app_distr || rewrite map_app); simpl.
    repeat ((rewrite filter_app in H)
            || (rewrite rev_app_distr in H)
            || (rewrite map_app in H)); simpl in H.
    unfold f2iValid in H0; rewrite H0; simpl.
    split; auto.
    rewrite <-H1; auto.
  Qed.

  Lemma pcChainFromDec_r2e_killed:
    forall pcv exeEpochv d2rv r2ev r2ee,
      pcChainFromDec pcv exeEpochv d2rv (r2ee :: r2ev) ->
      pcChainFromDec pcv exeEpochv d2rv r2ev.
  Proof.
    unfold pcChainFromDec, epochPcDre; intros.
    simpl in H.
    destruct (eqb _ _); auto.
    simpl in H.
    apply pcChain_app in H; dest; auto.
  Qed.

  (** [consistentDecEpoch] and [consistentExeEpoch] describe invariants
   * when a pc value is redirected from Decode or Execute, respectively,
   * saying that all epoch values are same throughout the fifos.
   *)
  Definition consistentDecEpochF2I (decEpoch: bool) (f2i: list (type (Struct F2I))) :=
    Forall (fun e : type (Struct F2I) => e Fin.F1 (Fin.FS (Fin.FS Fin.F1))
                                         = decEpoch) f2i.

  Definition consistentDecEpochI2D (decEpoch: bool) (i2d: list (type (Struct I2D))) :=
    Forall (fun e : type (Struct I2D) => e Fin.F1 (Fin.FS (Fin.FS Fin.F1))
                                         = decEpoch) i2d.

  Definition consistentDecEpoch (decEpoch: bool)
             (f2i: list (type (Struct F2I))) (i2d: list (type (Struct I2D))) :=
    consistentDecEpochF2I decEpoch f2i /\ consistentDecEpochI2D decEpoch i2d.

  Definition consistentExeEpochF2I (exeEpoch: bool) (f2i: list (type (Struct F2I))) :=
    Forall (fun e : type (Struct F2I) => e Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))
                                         = exeEpoch) f2i.

  Definition consistentExeEpochI2D (exeEpoch: bool) (i2d: list (type (Struct I2D))) :=
    Forall (fun e : type (Struct I2D) => e Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))
                                         = exeEpoch) i2d.

  Definition consistentExeEpochD2R (exeEpoch: bool) (d2r: list (type (Struct D2R))) :=
    Forall (fun e : type (Struct D2R) => e (Fin.FS (Fin.FS (Fin.FS Fin.F1))) = exeEpoch) d2r.

  Definition consistentExeEpochR2E (exeEpoch: bool) (r2e: list (type (Struct R2E))) :=
    Forall (fun e : type (Struct R2E) => e (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))
                                         = exeEpoch) r2e.

  Definition consistentExeEpoch (exeEpoch: bool)
             (f2i: list (type (Struct F2I))) (i2d: list (type (Struct I2D)))
             (d2r: list (type (Struct D2R))) (r2e: list (type (Struct R2E))) :=
    consistentExeEpochF2I exeEpoch f2i /\ consistentExeEpochI2D exeEpoch i2d /\
    consistentExeEpochD2R exeEpoch d2r /\ consistentExeEpochR2E exeEpoch r2e.

  (** Lemmas *)

  Lemma epochPcFidre_f2i_pass:
    forall f2iv f2ie i2dv i2de d2rv r2ev,
      f2ie Fin.F1 = i2de Fin.F1 ->
      epochPcFidre f2iv (i2dv ++ [i2de]) d2rv r2ev =
      epochPcFidre (f2ie :: f2iv) i2dv d2rv r2ev.
  Proof.
    unfold epochPcFidre; intros.
    do 2 f_equal.
    rewrite map_app; simpl.
    rewrite <-app_assoc.
    f_equal; simpl; f_equal.
    unfold f2iToEpochPc, i2dToEpochPc; simpl.
    rewrite H; reflexivity.
  Qed.

  Lemma consistentDecEpochF2I_filter_nil:
    forall decEpochv exeEpochv f2iv,
      consistentDecEpochF2I (negb decEpochv) f2iv ->
      filter (fun ep => decEpochMatches decEpochv (pDecEpoch ep) && eqb (pExeEpoch ep) exeEpochv)
             (map f2iToEpochPc f2iv) = nil.
  Proof.
    induction f2iv; simpl; intros; auto.
    inv H.
    destruct (a Fin.F1 (Fin.FS (Fin.FS Fin.F1))), decEpochv;
      try (inv H2; fail);
      try (simpl; auto).
  Qed.

  Lemma consistentDecEpochI2D_filter_nil:
    forall decEpochv exeEpochv i2dv,
      consistentDecEpochI2D (negb decEpochv) i2dv ->
      filter (fun ep => decEpochMatches decEpochv (pDecEpoch ep) && eqb (pExeEpoch ep) exeEpochv)
             (map i2dToEpochPc i2dv) = nil.
  Proof.
    induction i2dv; simpl; intros; auto.
    inv H.
    destruct (a Fin.F1 (Fin.FS (Fin.FS Fin.F1))), decEpochv;
      try (inv H2; fail);
      try (simpl; auto).
  Qed.

  Lemma consistentExeEpochF2I_filter_nil:
    forall decEpochv exeEpochv f2iv,
      consistentExeEpochF2I (negb exeEpochv) f2iv ->
      filter (fun ep => decEpochMatches decEpochv (pDecEpoch ep) && eqb (pExeEpoch ep) exeEpochv)
             (map f2iToEpochPc f2iv) = nil.
  Proof.
    induction f2iv; simpl; intros; auto.
    inv H.
    destruct (a Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))), exeEpochv;
      try (inv H2; fail);
      try (rewrite andb_false_r; auto).
  Qed.

  Lemma consistentExeEpochI2D_filter_nil:
    forall decEpochv exeEpochv i2dv,
      consistentExeEpochI2D (negb exeEpochv) i2dv ->
      filter (fun ep => decEpochMatches decEpochv (pDecEpoch ep) && eqb (pExeEpoch ep) exeEpochv)
             (map i2dToEpochPc i2dv) = nil.
  Proof.
    induction i2dv; simpl; intros; auto.
    inv H.
    destruct (a Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))), exeEpochv;
      try (inv H2; fail);
      try (rewrite andb_false_r; auto).
  Qed.

  Lemma consistentExeEpochD2R_filter_nil:
    forall decEpochv exeEpochv d2rv,
      consistentExeEpochD2R (negb exeEpochv) d2rv ->
      filter (fun ep => decEpochMatches decEpochv (pDecEpoch ep) && eqb (pExeEpoch ep) exeEpochv)
             (map d2rToEpochPc d2rv) = nil.
  Proof.
    induction d2rv; simpl; intros; auto.
    inv H.
    destruct (a (Fin.FS (Fin.FS (Fin.FS Fin.F1)))), exeEpochv;
      auto; inv H2.
  Qed.

  Lemma consistentExeEpochR2E_filter_nil:
    forall decEpochv exeEpochv r2ev,
      consistentExeEpochR2E (negb exeEpochv) r2ev ->
      filter (fun ep => decEpochMatches decEpochv (pDecEpoch ep) && eqb (pExeEpoch ep) exeEpochv)
             (map r2eToEpochPc r2ev) = nil.
  Proof.
    induction r2ev; simpl; intros; auto.
    inv H.
    destruct (a (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))), exeEpochv;
      auto; inv H2.
  Qed.

  Lemma pcChainFromPc_consistentExeEpoch_invalid:
    forall pcv decEpochv exeEpochv f2iv i2dv d2rv r2ev,
      consistentExeEpoch (negb exeEpochv) f2iv i2dv d2rv r2ev ->
      pcChainFromPc pcv decEpochv exeEpochv f2iv i2dv d2rv r2ev.
  Proof.
    unfold consistentExeEpoch, pcChainFromPc, epochPcFidre; intros; dest.
    repeat rewrite filter_app.
    rewrite consistentExeEpochF2I_filter_nil by assumption.
    rewrite consistentExeEpochI2D_filter_nil by assumption.
    rewrite consistentExeEpochD2R_filter_nil by assumption.
    rewrite consistentExeEpochR2E_filter_nil by assumption.
    simpl; auto.
  Qed.

  Lemma pcChainFromPc_consistentDecEpoch_invalid:
    forall pcv decEpochv exeEpochv f2iv i2dv d2rv r2ev,
      consistentDecEpoch (negb decEpochv) f2iv i2dv ->
      pcChainFromDec pcv exeEpochv d2rv r2ev ->
      pcChainFromPc pcv decEpochv exeEpochv f2iv i2dv d2rv r2ev.
  Proof.
    unfold consistentDecEpoch, pcChainFromDec, pcChainFromPc, epochPcDre, epochPcFidre;
      intros; dest.
    rewrite filter_app in H0.
    repeat rewrite filter_app.
    rewrite consistentDecEpochF2I_filter_nil by assumption.
    rewrite consistentDecEpochI2D_filter_nil by assumption.
    simpl; auto.
    rewrite app_nil_r.
    match goal with
    | [H: pcChain _ (List.rev (?r1 ++ ?d1)) |- pcChain _ (List.rev (?r2 ++ ?d2)) ] =>
      replace r2 with r1
    end.
    match goal with
    | [H: pcChain _ (List.rev (?r1 ++ ?d1)) |- pcChain _ (List.rev (?r2 ++ ?d2)) ] =>
      replace d2 with d1; auto
    end.
    - clear; induction d2rv; simpl; intros; auto.
      destruct (eqb _ _); auto.
      f_equal; auto.
    - clear; induction r2ev; simpl; intros; auto.
      destruct (eqb _ _); auto.
      f_equal; auto.
  Qed.

  Lemma getOldest_consistency_f2i_enq:
    forall (decEpochv exeEpochv: fullType type (SyntaxKind Bool))
           (decRedirv exeRedirv: fullType type (SyntaxKind (RedirectK addrSize)))
           f2iv (f2ie: type (Struct F2I)) i2dv d2rv r2ev,
      (exeRedirv Fin.F1 = false -> f2ie Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1))) = exeEpochv) ->
      (f2ie Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1))) = exeEpochv -> exeRedirv Fin.F1 = false) ->
      match getOldest f2iv i2dv d2rv r2ev with
      | Some ep =>
        pExeEpoch ep = exeEpochv ->
        exeRedirv Fin.F1 = false /\ consistentExeEpoch exeEpochv f2iv i2dv d2rv r2ev
      | None => True
      end ->
      match getOldest (f2iv ++ [f2ie]) i2dv d2rv r2ev with
      | Some ep =>
        pExeEpoch ep = exeEpochv ->
        exeRedirv Fin.F1 = false /\ consistentExeEpoch exeEpochv (f2iv ++ [f2ie]) i2dv d2rv r2ev
      | None => True
      end.
  Proof.
    unfold getOldest, epochPcFidre, consistentExeEpoch; intros.
    destruct r2ev;
      [|simpl; simpl in H1; intros; specialize (H1 H2); dest; repeat split; auto;
        apply ListSupport.Forall_app; auto].
    destruct d2rv;
      [|simpl; simpl in H1; intros; specialize (H1 H2); dest; repeat split; auto;
        apply ListSupport.Forall_app; auto].
    destruct i2dv;
      [|simpl; simpl in H1; intros; specialize (H1 H2); dest; repeat split; auto;
        apply ListSupport.Forall_app; auto].
    simpl; simpl in H1.
    rewrite map_app; simpl.
    match goal with
    | [H: context[match (map _ ?l) with | nil => _ | _ => _ end] |- _] => destruct l
    end.
    - simpl; intros.
      repeat split; repeat constructor; auto.
    - simpl; simpl in H1; intros; specialize (H1 H2); dest; repeat split; auto.
      inv H3.
      constructor; auto.
      apply ListSupport.Forall_app; auto.
  Qed.

  Lemma consistentExeEpoch_getOldest:
    forall exeEpochv f2iv i2dv d2rv r2ev ep,
      consistentExeEpoch exeEpochv f2iv i2dv d2rv r2ev ->
      getOldest f2iv i2dv d2rv r2ev = Some ep ->
      pExeEpoch ep = exeEpochv.
  Proof.
    unfold consistentExeEpoch, getOldest, epochPcFidre; intros; dest.
    destruct r2ev as [|r2ee ?]; simpl in H0.
    - destruct d2rv as [|d2re ?]; simpl in H0.
      + destruct i2dv as [|i2de ?]; simpl in H0.
        * destruct f2iv as [|f2ie ?]; simpl in H0; try discriminate.
          inv H0; inv H; reflexivity.
        * inv H0; inv H1; reflexivity.
      + inv H0; inv H2; reflexivity.
    - inv H0; inv H3; reflexivity.
  Qed.

  Lemma consistentDecEpoch_pass_valid:
    forall decEpochv f2iv f2ie i2dv i2de,
      f2ie Fin.F1 = i2de Fin.F1 ->
      consistentDecEpoch decEpochv (f2ie :: f2iv) i2dv ->
      consistentDecEpoch decEpochv f2iv (i2dv ++ [i2de]).
  Proof.
    unfold consistentDecEpoch; intros; dest.
    inv H0.
    split; auto.
    apply ListSupport.Forall_app; auto.
    rewrite H; auto.
  Qed.

  Lemma consistentDecEpoch_killed_valid:
    forall decEpochv f2iv i2dv i2de,
      consistentDecEpoch decEpochv f2iv (i2de :: i2dv) ->
      consistentDecEpoch decEpochv f2iv i2dv.
  Proof.
    unfold consistentDecEpoch; intros; dest.
    inv H0.
    split; auto.
  Qed.

  Lemma consistentExeEpoch_f2i_pass_valid:
    forall exeEpochv f2iv f2ie i2dv i2de d2rv r2ev,
      f2ie Fin.F1 = i2de Fin.F1 ->
      consistentExeEpoch exeEpochv (f2ie :: f2iv) i2dv d2rv r2ev ->
      consistentExeEpoch exeEpochv f2iv (i2dv ++ [i2de]) d2rv r2ev.
  Proof.
    unfold consistentExeEpoch; intros; dest.
    inv H0.
    repeat split; auto.
    apply ListSupport.Forall_app; auto.
    rewrite H; auto.
  Qed.

  Lemma consistentExeEpoch_i2d_pass_valid:
    forall exeEpochv f2iv i2dv (i2de: type (Struct I2D)) d2rv (d2re: type (Struct D2R)) r2ev,
      i2de Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1))) =
      d2re (Fin.FS (Fin.FS (Fin.FS Fin.F1))) ->
      consistentExeEpoch exeEpochv f2iv (i2de :: i2dv) d2rv r2ev ->
      consistentExeEpoch exeEpochv f2iv i2dv (d2rv ++ [d2re]) r2ev.
  Proof.
    unfold consistentExeEpoch; intros; dest.
    inv H1.
    repeat split; auto.
    apply ListSupport.Forall_app; auto.
  Qed.

  Lemma consistentExeEpoch_i2d_killed_valid:
    forall exeEpochv f2iv i2dv i2de d2rv r2ev,
      consistentExeEpoch exeEpochv f2iv (i2de :: i2dv) d2rv r2ev ->
      consistentExeEpoch exeEpochv f2iv i2dv d2rv r2ev.
  Proof.
    unfold consistentExeEpoch; intros; dest.
    inv H0.
    repeat split; auto.
  Qed.

  Lemma consistentExeEpoch_r2e_killed:
    forall exeEpochv f2iv i2dv d2rv r2ev r2ee,
      consistentExeEpoch exeEpochv f2iv i2dv d2rv (r2ee :: r2ev) ->
      consistentExeEpoch exeEpochv f2iv i2dv d2rv r2ev.
  Proof.
    unfold consistentExeEpoch; intros; dest.
    inv H2; auto.
  Qed.

  Lemma pcChainFromPc_f2i_pass_valid:
    forall pcv decEpochv exeEpochv f2iv f2ie i2dv i2de d2rv r2ev,
      f2ie Fin.F1 = i2de Fin.F1 ->
      pcChainFromPc pcv decEpochv exeEpochv (f2ie :: f2iv) i2dv d2rv r2ev ->
      pcChainFromPc pcv decEpochv exeEpochv f2iv (i2dv ++ [i2de]) d2rv r2ev.
  Proof.
    unfold pcChainFromPc; intros.
    erewrite epochPcFidre_f2i_pass; eauto.
  Qed.

  Lemma pcChainFromPc_i2d_killed:
    forall pcv decEpochv exeEpochv f2iv i2dv d2rv r2ev (i2de: type (Struct I2D)),
      (if bool_dec exeEpochv (i2de Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
       then true else false)
        && (if bool_dec decEpochv (i2de Fin.F1 (Fin.FS (Fin.FS Fin.F1)))
            then true else false) = false ->
      pcChainFromPc pcv decEpochv exeEpochv f2iv (i2de :: i2dv) d2rv r2ev ->
      pcChainFromPc pcv decEpochv exeEpochv f2iv i2dv d2rv r2ev.
  Proof.
    unfold pcChainFromPc; intros.
    replace (filter (fun ep => (decEpochMatches decEpochv (pDecEpoch ep))
                                 && (eqb (pExeEpoch ep) exeEpochv))
                    (epochPcFidre f2iv i2dv d2rv r2ev)) with
    (filter
       (fun ep => (decEpochMatches decEpochv (pDecEpoch ep))
                    && (eqb (pExeEpoch ep) exeEpochv))
       (epochPcFidre f2iv (i2de :: i2dv) d2rv r2ev)); auto.
    unfold epochPcFidre.
    repeat rewrite filter_app.
    do 3 f_equal; simpl.
    destruct decEpochv, exeEpochv,
    (i2de Fin.F1 (Fin.FS (Fin.FS Fin.F1))), (i2de Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1))));
      simpl; try discriminate; auto.
  Qed.

  Lemma pcChainFromPc_r2e_killed:
    forall pcv decEpochv exeEpochv f2iv i2dv d2rv r2ev r2ee,
      pcChainFromPc pcv decEpochv exeEpochv f2iv i2dv d2rv (r2ee :: r2ev) ->
      pcChainFromPc pcv decEpochv exeEpochv f2iv i2dv d2rv r2ev.
  Proof.
    unfold pcChainFromPc, epochPcFidre; intros.
    simpl in H.
    destruct (eqb _ _); auto.
    simpl in H.
    apply pcChain_app in H; dest; auto.
  Qed.

  Lemma getOldest_f2i_pass_valid:
    forall f2iv f2ie i2dv i2de d2rv r2ev,
      f2ie Fin.F1 = i2de Fin.F1 ->
      getOldest f2iv (i2dv ++ [i2de]) d2rv r2ev =
      getOldest (f2ie :: f2iv) i2dv d2rv r2ev.
  Proof.
    unfold getOldest; intros.
    erewrite epochPcFidre_f2i_pass; eauto.
  Qed.

  Record epoch_invariant (o: RegsT) : Prop :=
    { pcv : fullType type (SyntaxKind (Bit addrSize));
      Hpc: M.find "pc" o = Some (existT _ _ pcv);
      fetchEpochDv : fullType type (SyntaxKind Bool);
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

      f2iv : fullType type (@NativeKind (list (type (Struct F2I))) nil);
      Hf2iv : M.find (f2iName -- Names.elt) o = Some (existT _ _ f2iv);
      i2dv : fullType type (@NativeKind (list (type (Struct I2D))) nil);
      Hi2dv : M.find (i2dName -- Names.elt) o = Some (existT _ _ i2dv);
      d2rv : fullType type (@NativeKind (list (type (Struct D2R))) nil);
      Hd2rv : M.find (d2rName -- Names.elt) o = Some (existT _ _ d2rv);
      r2ev : fullType type (@NativeKind (list (type (Struct R2E))) nil);
      Hr2ev : M.find (r2eName -- Names.elt) o = Some (existT _ _ r2ev);

      (** Relation between epoch values and redirections *)
      HdeSpec1: fetchEpochDv = decEpochv -> decRedirv Fin.F1 (* isValid *) = false;
      HdeSpec2: decRedirv Fin.F1 = false -> fetchEpochDv = decEpochv;

      HeeSpec1: fetchEpochEv = exeEpochv -> exeRedirv Fin.F1 = false;
      HeeSpec2: exeRedirv Fin.F1 = false -> fetchEpochEv = exeEpochv;

      (** Invariants when some redirections exist *)
      HdrSpec: decRedirv Fin.F1 = true ->
               consistentDecEpoch (negb decEpochv) f2iv i2dv;
      HerSpec: exeRedirv Fin.F1 = true ->
               consistentExeEpoch (negb exeEpochv) f2iv i2dv d2rv r2ev;

      (** Invariants about pc/predPc chain *)
      Hchain1: decRedirv Fin.F1 = true ->
               exeRedirv Fin.F1 = false ->
               pcChainFromDec (decRedirv (Fin.FS Fin.F1) (Fin.FS Fin.F1)) exeEpochv d2rv r2ev;
      Hchain2: decRedirv Fin.F1 = false ->
               exeRedirv Fin.F1 = false ->
               pcChainFromPc pcv decEpochv exeEpochv f2iv i2dv d2rv r2ev;

      (** An invariant about exeEpoch *)
      HeeSpec3: match getOldest f2iv i2dv d2rv r2ev with
                | Some ep => pExeEpoch ep = exeEpochv ->
                             exeRedirv Fin.F1 = false /\
                             consistentExeEpoch exeEpochv f2iv i2dv d2rv r2ev
                | None => True
                end
    }.

  Local Notation "'_STRUCT_'" := (fun i : Fin.t _ => _).
  Local Notation "'_STRUCT_SIG_'" := (forall i : Fin.t _, _).

  Lemma fidreComb_epoch_invariant_ok:
    forall o, reachable o fidreComb -> epoch_invariant o.
  Proof.
    intros; apply stepInv with (m:= fidreComb); auto.

    Focus 1. (* initial case *)
    econstructor;
      try (findReify; (reflexivity || eassumption); fail);
      auto.
    intros; inv H0.
    intros; inv H0.
    vm_compute; auto.
    vm_compute; auto.
    vm_compute; auto.

    (* induction case *)
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
      + intros.
        specialize (HdrSpec H); unfold consistentDecEpoch in HdrSpec; dest.
        constructor; auto.
        apply ListSupport.Forall_app; auto.
        constructor; auto.
        inv H2.
        destruct (decRedirv Fin.F1); try discriminate.
        destruct x2, decEpochv; auto; try discriminate.
        specialize (HdeSpec1 eq_refl); discriminate.
      + intros.
        specialize (HerSpec H); unfold consistentExeEpoch in HerSpec; dest.
        constructor; auto.
        apply ListSupport.Forall_app; auto.
        constructor; auto.
        inv H2.
        destruct (exeRedirv Fin.F1); try discriminate.
        destruct x3, exeEpochv; auto; try discriminate.
        specialize (HeeSpec1 eq_refl); discriminate.
      + intros; inv H2; eapply pcChainFromPc_f2i_enq; try reflexivity.
        * eauto.
        * unfold f2iValid; simpl.
          specialize (HdeSpec2 H); specialize (HeeSpec2 H0); subst.
          rewrite 2! eqb_reflx; auto.
      + apply getOldest_consistency_f2i_enq; auto;
          try (inv H2; auto).

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
      + intros; inv H.
      + intros; inv H.
      + intros; inv H.
      + intros; inv H6.
        specialize (HerSpec H4).
        apply pcChainFromPc_consistentExeEpoch_invalid; auto.
      + destruct (getOldest f2iv i2dv d2rv r2ev); auto.
        intros; specialize (HeeSpec3 H); dest.
        split; auto.

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
      + intros; inv H.
      + intros; inv H.
      + intros; inv H1.
        specialize (Hchain1 H6 H0).
        specialize (HdrSpec H6).
        apply pcChainFromPc_consistentDecEpoch_invalid; auto.
        
    - (* doIMem *)
      kinv_action_dest.
      kinv_red; kregmap_red.
      kinvert_det; kinv_action_dest.
      destruct H.
      kinv_red; kregmap_red; kinv_red.
      
      econstructor;
        try (findReify; try (reflexivity || eassumption); fail);
        try assumption.
      + destruct x3 as [|f2ie ?]; try discriminate.
        intros; specialize (HdrSpec H).
        eapply consistentDecEpoch_pass_valid; eauto.
        inv H1; inv H4; reflexivity.
      + destruct x3 as [|f2ie ?]; try discriminate.
        intros; specialize (HerSpec H).
        eapply consistentExeEpoch_f2i_pass_valid; eauto.
        inv H1; inv H4; reflexivity.
      + destruct x3 as [|f2ie ?]; try discriminate.
        intros; specialize (Hchain2 H H0).
        eapply pcChainFromPc_f2i_pass_valid; eauto.
        inv H1; inv H4; reflexivity.
      + destruct x3 as [|f2ie ?]; try discriminate.
        inv H1; inv H4.
        rewrite getOldest_f2i_pass_valid with (f2ie:= f2ie) by reflexivity.
        destruct (getOldest _ _ _ _); auto.
        intros; specialize (HeeSpec3 H); dest.
        split; auto.
        eapply consistentExeEpoch_f2i_pass_valid; eauto.

    - (* killDecode *)
      kinv_action_dest.
      kinv_red; kregmap_red.
      kinvert_det; kinv_action_dest.
      destruct H.
      kinv_red; kregmap_red; kinv_red.
      
      econstructor;
        try (findReify; try (reflexivity || eassumption); fail);
        try assumption.
      + destruct x3 as [|i2de ?]; try discriminate.
        intros; specialize (HdrSpec H).
        eapply consistentDecEpoch_killed_valid; eauto.
      + destruct x3 as [|i2de ?]; try discriminate.
        intros; specialize (HerSpec H).
        eapply consistentExeEpoch_i2d_killed_valid; eauto.
      + destruct x3 as [|i2de ?]; try discriminate.
        intros; specialize (Hchain2 H H0).
        inv H2; inv H5.
        eapply pcChainFromPc_i2d_killed; eauto.
      + destruct x3 as [|i2de ?]; try discriminate.
        admit. (* need a new invariant *)

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
        * destruct x7 as [|i2de ?]; try discriminate.
          (* need the same invariant for [consistentDecEpoch] related to [getOldest] *)
          admit.
        * destruct x7 as [|r2ee ?]; try discriminate.
          inv H2; inv H5; inv H11; inv H14.
          intros; specialize (HerSpec H).
          eapply consistentExeEpoch_i2d_pass_valid; eauto.
        * destruct x7 as [|r2ee ?]; try discriminate.
          inv H2; inv H5; inv H11; inv H14.
          intros. specialize (Hchain2 e H0).
          move Hchain2 at bottom.
          admit. (* provable using Hchain2 *)
        * intros; inv H.
        * destruct x7 as [|r2ee ?]; try discriminate.
          admit. (* provable using HeeSpec3 *)

      + destruct H.
        kinv_red; kregmap_red; kinv_red.
        econstructor;
          try (findReify; try (reflexivity || eassumption); fail);
          try assumption.
        * destruct x5 as [|r2ee ?]; try discriminate.
          intros; specialize (HdrSpec H).
          eapply consistentDecEpoch_killed_valid; eauto.
        * destruct x5 as [|r2ee ?]; try discriminate.
          intros; specialize (HerSpec H).
          inv H2; inv H5; inv H7.
          eapply consistentExeEpoch_i2d_pass_valid; eauto.
        * (* need the same invariant for [consistentDecEpoch] related to [getOldest] *)
          admit.
        * destruct x5 as [|r2ee ?]; try discriminate.
          intros; specialize (Hchain2 H H0).
          admit. (* provable using Hchain2 *)
        * destruct x5 as [|r2ee ?]; try discriminate.
          admit. (* provable using HeeSpec3 *)

    - (* doRegRead *)
      kinv_action_dest.
      kinv_red; kregmap_red.
      kinvert_det; kinv_action_dest.
      destruct H.
      kinv_red; kregmap_red; kinv_red.
      
      econstructor;
        try (findReify; try (reflexivity || eassumption); fail);
        try assumption.
      + admit. (* provable - just simple pass case *)
      + admit. (* provable - just simple pass case *)
      + admit. (* provable - just simple pass case *)
      + admit. (* provable - just simple pass case *)

    - (* killExecute *)
      kinv_action_dest.
      kinv_red; kregmap_red.
      kinvert_det; kinv_action_dest.
      destruct H.
      kinv_red; kregmap_red; kinv_red.
      
      econstructor;
        try (findReify; try (reflexivity || eassumption); fail);
        try assumption.
      + destruct x3 as [|r2ee ?]; try discriminate.
        intros; specialize (HerSpec H).
        apply consistentExeEpoch_r2e_killed with (r2ee:= r2ee); auto.
      + destruct x3 as [|r2ee ?]; try discriminate.
        intros; specialize (Hchain1 H H0).
        eapply pcChainFromDec_r2e_killed; eauto.
      + destruct x3 as [|r2ee ?]; try discriminate.
        intros; specialize (Hchain2 H H0).
        eapply pcChainFromPc_r2e_killed; eauto.
      + destruct x3 as [|r2ee ?]; try discriminate.
        admit. (* TODO: need a new invariant :( *)

    - (* doExecute *)
      kinv_action_dest;
        kinv_red; kregmap_red;
          kinvert_det; kinv_action_dest.
      
      + (* case redirected *)
        destruct H.
        kinv_red; kregmap_red; kinv_red.
        econstructor;
          try (findReify; try (reflexivity || eassumption); fail);
          try assumption.
        * specialize (HeeSpec2 e).
          subst; intros.
          exfalso; eapply no_fixpoint_negb; eauto.
        * intros; discriminate.
        * destruct x7 as [|r2ee ?]; try discriminate.
          intros; simpl in HeeSpec3.
          inv H1; inv H4; inv H8; inv H11.
          specialize (HeeSpec3 eq_refl); dest.
          rewrite negb_involutive.
          eapply consistentExeEpoch_r2e_killed; eauto.
        * intros; inv H0.
        * intros; inv H0.
        * destruct x7 as [|r2ee ?]; try discriminate.
          inv H1; inv H4; inv H8; inv H11.
          simpl in HeeSpec3; specialize (HeeSpec3 eq_refl); dest.
          case_eq (getOldest f2iv i2dv d2rv x7); intros; auto.
          exfalso.
          apply consistentExeEpoch_r2e_killed in H0.
          eapply consistentExeEpoch_getOldest in H1; eauto.
          rewrite H1 in H2; eapply negb_eq_false; eauto.

      + (* case not redirected *)
        destruct H.
        kinv_red; kregmap_red; kinv_red.
        econstructor;
          try (findReify; try (reflexivity || eassumption); fail);
          try assumption.
        * destruct x2 as [|r2ee ?]; try discriminate.
          intros; specialize (HerSpec H).
          eapply consistentExeEpoch_r2e_killed; eauto.
        * destruct x2 as [|r2ee ?]; try discriminate.
          intros; specialize (Hchain1 H H0).
          eapply pcChainFromDec_r2e_killed; eauto.
        * destruct x2 as [|r2ee ?]; try discriminate.
          intros; specialize (Hchain2 H H0).
          eapply pcChainFromPc_r2e_killed; eauto.
        * destruct x2 as [|r2ee ?]; try discriminate.
          inv H1; inv H4.
          simpl in HeeSpec3; specialize (HeeSpec3 eq_refl); dest.
          destruct (getOldest f2iv i2dv d2rv x2); auto; intros.
          split; auto.
          eapply consistentExeEpoch_r2e_killed; eauto.
  Admitted.
  
End Processor.


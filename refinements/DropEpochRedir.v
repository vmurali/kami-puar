Require Import Kami.
Require Import Lib.CommonTactics Lib.Indexer Lib.VectorFacts.
Require Import Kami.Decomposition Kami.ModuleBoundEx.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import Proc.AbstractIsa Proc.Fetch Proc.Decode Proc.RegRead Proc.Execute
        Proc.InOrderEightStage.
Require Import DropBranchPredictors Fidre EpochInv.

Require Import StepDet. (* TODO: should move to Kami *)

Set Implicit Arguments.
Open Scope string.
Open Scope list.

Section Processor.
  Variables addrSize dataBytes rfIdx: nat.

  Variable decodeInst: DecodeT dataBytes rfIdx.
  Variable execInst: ExecT addrSize dataBytes rfIdx.

  (** Fetch related *)
  Definition fetchNondetNR := fetchNondetNR addrSize dataBytes.
  Definition f2i := f2i addrSize dataBytes.

  (** IMem related *)
  Definition iMem := iMem addrSize dataBytes.
  Definition i2d := i2d addrSize dataBytes.

  (** Decode related *)
  Definition decodeNondetNR := decodeNondetNR addrSize decodeInst.
  Definition d2r := d2r addrSize dataBytes rfIdx.

  (** RegRead related *)
  Definition regRead := regRead addrSize dataBytes rfIdx.
  Definition r2e := r2e addrSize dataBytes rfIdx.

  (** Execute related *)
  Definition executeNondetNR := executeNondetNR execInst.

  Definition fidreComb := fidreComb decodeInst execInst.
  
  Definition fidreNR :=
    (fetchNondetNR ++ f2i
                   ++ iMem ++ i2d
                   ++ decodeNondetNR ++ d2r
                   ++ regRead ++ r2e
                   ++ executeNondetNR)%kami.

  Definition F2I := F2I addrSize dataBytes.
  Definition I2D := I2D addrSize dataBytes.
  Definition D2R := D2R addrSize dataBytes rfIdx.
  Definition R2E := R2E addrSize dataBytes rfIdx.

  (* Construction of the state relation [thetaR] *)

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

  Fixpoint getArchPcF2I (decEpoch exeEpoch: bool) (f2i: list (type (Struct F2I)))
    : option (fullType type (SyntaxKind (Bit addrSize))) :=
    match f2i with
    | nil => None
    | e :: f2i' =>
      if f2iValid decEpoch exeEpoch e
      then Some (e Fin.F1 Fin.F1)
      else getArchPcF2I decEpoch exeEpoch f2i'
    end.

  Lemma getArchPcF2I_app:
    forall decEpochv exeEpochv (f2iv1 f2iv2: list (type (Struct F2I))),
      getArchPcF2I decEpochv exeEpochv (f2iv1 ++ f2iv2) =
      match getArchPcF2I decEpochv exeEpochv f2iv1 with
      | Some v => Some v
      | None => getArchPcF2I decEpochv exeEpochv f2iv2
      end.
  Proof.
    induction f2iv1; intros; auto.
    simpl.
    destruct (f2iValid decEpochv exeEpochv a); auto.
  Qed.

  Fixpoint getArchPcI2D (decEpoch exeEpoch: bool) (i2d: list (type (Struct I2D)))
    : option (fullType type (SyntaxKind (Bit addrSize))) :=
    match i2d with
    | nil => None
    | e :: i2d' =>
      if i2dValid decEpoch exeEpoch e
      then Some (e Fin.F1 Fin.F1)
      else getArchPcI2D decEpoch exeEpoch i2d'
    end.

  Lemma getArchPcI2D_app:
    forall decEpochv exeEpochv (i2dv1 i2dv2: list (type (Struct I2D))),
      getArchPcI2D decEpochv exeEpochv (i2dv1 ++ i2dv2) =
      match getArchPcI2D decEpochv exeEpochv i2dv1 with
      | Some v => Some v
      | None => getArchPcI2D decEpochv exeEpochv i2dv2
      end.
  Proof.
    induction i2dv1; intros; auto.
    simpl.
    destruct (i2dValid decEpochv exeEpochv a); auto.
  Qed.

  Fixpoint getArchPcD2R (exeEpoch: bool) (d2r: list (type (Struct D2R)))
    : option (fullType type (SyntaxKind (Bit addrSize))) :=
    match d2r with
    | nil => None
    | e :: d2r' =>
      if d2rValid exeEpoch e
      then Some (e Fin.F1)
      else getArchPcD2R exeEpoch d2r'
    end.

  Fixpoint getArchPcR2E (exeEpoch: bool) (r2e: list (type (Struct R2E)))
    : option (fullType type (SyntaxKind (Bit addrSize))) :=
    match r2e with
    | nil => None
    | e :: r2e' =>
      if r2eValid exeEpoch e
      then Some (e Fin.F1)
      else getArchPcR2E exeEpoch r2e'
    end.

  Local Definition otake {A} (oa: option A) (default: A): A :=
    match oa with
    | Some a => a
    | None => default
    end.
  Infix ">>=" := otake (at level 0, right associativity).

  Definition maybeToOption {k} (mb: fullType type (SyntaxKind (Struct (Maybe k))))
    : option (fullType type (SyntaxKind k)) :=
    if mb Fin.F1 then Some (mb (Fin.FS Fin.F1)) else None.

  Definition getPcRedir (redir: fullType type (SyntaxKind (RedirectK addrSize)))
    : option (fullType type (SyntaxKind (Bit addrSize))) :=
    match maybeToOption redir with
    | Some rd => Some (rd (Fin.FS Fin.F1))
    | None => None
    end.

  Definition getArchPc (pcv: fullType type (SyntaxKind (Bit addrSize)))
             (decEpoch exeEpoch: fullType type (SyntaxKind Bool))
             (decRedir exeRedir: fullType type (SyntaxKind (RedirectK addrSize)))
             (f2i: fullType type (@NativeKind (list (type (Struct F2I))) nil))
             (i2d: fullType type (@NativeKind (list (type (Struct I2D))) nil))
             (d2r: fullType type (@NativeKind (list (type (Struct D2R))) nil))
             (r2e: fullType type (@NativeKind (list (type (Struct R2E))) nil)) :=
    (getPcRedir exeRedir)
      >>= (getArchPcR2E exeEpoch r2e)
      >>= (getArchPcD2R exeEpoch d2r)
      >>= (getPcRedir decRedir)
      >>= (getArchPcI2D decEpoch exeEpoch i2d)
      >>= (getArchPcF2I decEpoch exeEpoch f2i)
      >>= pcv.

  Lemma getArchPc_f2i_valid:
    forall pcv pcv' decEpochv exeEpochv decRedirv exeRedirv
           f2iv (f2ie: fullType type (SyntaxKind (Struct F2I))) i2dv d2rv r2ev,
      f2ie Fin.F1 Fin.F1 = pcv ->
      f2iValid decEpochv exeEpochv f2ie = true ->
      getArchPc pcv decEpochv exeEpochv decRedirv exeRedirv f2iv i2dv d2rv r2ev =
      getArchPc pcv' decEpochv exeEpochv decRedirv exeRedirv (f2iv ++ [f2ie]) i2dv d2rv r2ev.
  Proof.
    unfold getArchPc; intros.
    destruct (getPcRedir exeRedirv); auto; simpl.
    destruct (getArchPcR2E exeEpochv r2ev); auto; simpl.
    destruct (getArchPcD2R exeEpochv d2rv); auto; simpl.
    destruct (getPcRedir decRedirv); auto; simpl.
    destruct (getArchPcI2D decEpochv exeEpochv i2dv); auto; simpl.
    rewrite getArchPcF2I_app.
    destruct (getArchPcF2I decEpochv exeEpochv f2iv); auto; simpl.
    rewrite H0; auto.
  Qed.

  Lemma getArchPc_exeRedir:
    forall pcv decEpochv exeEpochv decRedirv exeRedirv f2iv i2dv d2rv r2ev
           pcv' decEpochv' exeEpochv' decRedirv' f2iv' i2dv' d2rv' r2ev',
      maybeToOption exeRedirv <> None ->
      getArchPc pcv decEpochv exeEpochv decRedirv exeRedirv f2iv i2dv d2rv r2ev =
      getArchPc pcv' decEpochv' exeEpochv' decRedirv' exeRedirv f2iv' i2dv' d2rv' r2ev'.
  Proof.
    unfold getArchPc, getPcRedir; intros.
    destruct (maybeToOption exeRedirv); auto; simpl.
    elim H; reflexivity.
  Qed.

  Lemma getArchPc_decRedir:
    forall pcv decEpochv exeEpochv decRedirv exeRedirv f2iv i2dv d2rv r2ev
           pcv' decEpochv' f2iv' i2dv',
      maybeToOption decRedirv <> None ->
      getArchPc pcv decEpochv exeEpochv decRedirv exeRedirv f2iv i2dv d2rv r2ev =
      getArchPc pcv' decEpochv' exeEpochv decRedirv exeRedirv f2iv' i2dv' d2rv r2ev.
  Proof.
    unfold getArchPc, getPcRedir; intros.
    destruct (maybeToOption exeRedirv); auto; simpl.
    destruct (getArchPcR2E exeEpochv r2ev); auto; simpl.
    destruct (getArchPcD2R exeEpochv d2rv); auto; simpl.
    destruct (maybeToOption decRedirv); auto; simpl.
    elim H; reflexivity.
  Qed.

  Lemma getArchPc_exe_redirected:
    forall pcv decEpochv exeEpochv decRedirv exeRedirv f2iv i2dv d2rv r2ev
           (decRedirv' exeRedirv': fullType type (SyntaxKind (RedirectK addrSize))),
      consistentExeEpoch (negb exeEpochv) f2iv i2dv d2rv r2ev ->
      exeRedirv' Fin.F1 = false -> decRedirv' Fin.F1 = false ->
      getArchPc pcv decEpochv exeEpochv decRedirv exeRedirv f2iv i2dv d2rv r2ev =
      getArchPc (exeRedirv (Fin.FS Fin.F1) (Fin.FS Fin.F1)) decEpochv exeEpochv
                decRedirv' exeRedirv' f2iv i2dv d2rv r2ev.
  Proof.
  Admitted.

  Lemma getArchPc_dec_redirected:
    forall pcv decEpochv exeEpochv decRedirv exeRedirv f2iv i2dv d2rv r2ev
           (decRedirv': fullType type (SyntaxKind (RedirectK addrSize))),
      consistentDecEpoch (negb decEpochv) f2iv i2dv ->
      decRedirv' Fin.F1 = false ->
      getArchPc pcv decEpochv exeEpochv decRedirv exeRedirv f2iv i2dv d2rv r2ev =
      getArchPc (decRedirv (Fin.FS Fin.F1) (Fin.FS Fin.F1)) decEpochv exeEpochv
                decRedirv' exeRedirv f2iv i2dv d2rv r2ev.
  Proof.
  Admitted.

  Lemma getArchPc_iMem_pass:
    forall pcv decEpochv exeEpochv decRedirv exeRedirv
           f2iv (f2ie: fullType type (SyntaxKind (Struct F2I)))
           i2dv (i2de: fullType type (SyntaxKind (Struct I2D))) d2rv r2ev,
      f2ie Fin.F1 = i2de Fin.F1 ->
      getArchPc pcv decEpochv exeEpochv decRedirv exeRedirv (f2ie :: f2iv) i2dv d2rv r2ev =
      getArchPc pcv decEpochv exeEpochv decRedirv exeRedirv f2iv (i2dv ++ [i2de]) d2rv r2ev.
  Proof.
    unfold getArchPc; intros.
    rewrite getArchPcI2D_app; simpl.
    unfold f2iValid, i2dValid.
    rewrite H.
    destruct (getArchPcI2D decEpochv exeEpochv i2dv); auto; simpl.
    destruct (eqb _ _ && eqb _ _); auto.
  Qed.

  Lemma getArchPc_decode_killed:
    forall pcv decEpochv exeEpochv decRedirv exeRedirv
           f2iv i2dv (i2de: fullType type (SyntaxKind (Struct I2D))) d2rv r2ev,
      i2dValid decEpochv exeEpochv i2de = false ->
      getArchPc pcv decEpochv exeEpochv decRedirv exeRedirv f2iv (i2de :: i2dv) d2rv r2ev =
      getArchPc pcv decEpochv exeEpochv decRedirv exeRedirv f2iv i2dv d2rv r2ev.
  Proof.
    unfold getArchPc; intros.
    simpl; rewrite H; reflexivity.
  Qed.

  Local Definition thetaR (ir sr: RegsT): Prop.
  Proof.
    kexistnv "pc" pcv ir (SyntaxKind (Bit addrSize)).
    kexistnv "decEpoch" decEpochv ir (SyntaxKind Bool).
    kexistnv "exeEpoch" exeEpochv ir (SyntaxKind Bool).
    kexistnv "dec" decRedirv ir (SyntaxKind (RedirectK addrSize)).
    kexistnv "exe" exeRedirv ir (SyntaxKind (RedirectK addrSize)).
    kexistnv (f2iName -- Names.elt) f2iv ir (@NativeKind (list (type (Struct F2I))) nil).
    kexistnv (i2dName -- Names.elt) i2dv ir (@NativeKind (list (type (Struct I2D))) nil).
    kexistnv (d2rName -- Names.elt) d2rv ir (@NativeKind (list (type (Struct D2R))) nil).
    kexistnv (r2eName -- Names.elt) r2ev ir (@NativeKind (list (type (Struct R2E))) nil).
    exact (sr =
           ["pc" <- existT _ _ pcv]
           +[(f2iName -- Names.elt) <- existT _ _ f2iv]
           +[(i2dName -- Names.elt) <- existT _ _ i2dv]
           +[(d2rName -- Names.elt) <- existT _ _ d2rv]
           +[(r2eName -- Names.elt) <- existT _ _ r2ev]
           +["archPc" <- existT _ _ (getArchPc pcv decEpochv exeEpochv decRedirv exeRedirv
                                               f2iv i2dv d2rv r2ev)])%fmap.
  Defined.

  Hint Unfold F2I I2D D2R R2E : MethDefs.
  Hint Unfold thetaR : InvDefs.

  Local Notation "'_STRUCT_'" := (fun i : Fin.t _ => _).
  Local Notation "'_STRUCT_SIG_'" := (forall i : Fin.t _, _).

  Theorem fidreComb_fidreNR: fidreComb <<== fidreNR.
  Proof.
    apply stepRefinementR with (thetaR:= thetaR).
    - kdecompose_regrel_init.
      meqReify.

    - intros.
      apply fidreComb_epoch_invariant_ok in H.
      
      apply step_implies_stepDet in H0;
        [|kequiv|repeat (constructor || reflexivity)|reflexivity].

      inv H0; simpl;
        [do 2 eexists; split; [apply SemFacts.step_empty; auto|auto] (* empty rule *)
        |exists None; eexists; split; [apply SemFacts.step_empty; auto|auto] (* empty meth *)
        |].

      unfold thetaR in H1; dest; subst; subst.
      kinvert.
      
      + (* doFetch *)
        kinv_action_dest.
        kinv_red; kregmap_red.
        kinvert_det; kinv_action_dest.
        destruct H.
        kinv_red; kregmap_red; kinv_red.

        exists (Some "doFetch").
        kinv_constr_det; kinv_eq_light; auto.
        * destruct (bool_dec x12 x1); subst.
          { destruct (bool_dec x11 x0); subst.
            { inv H3; apply getArchPc_f2i_valid; auto.
              unfold f2iValid; simpl.
              rewrite 2! eqb_reflx; reflexivity.
            }
            { apply getArchPc_decRedir.
              unfold maybeToOption.
              destruct (x2 Fin.F1); auto.
              discriminate.
            }
          }
          { apply getArchPc_exeRedir.
            unfold maybeToOption.
            destruct (x3 Fin.F1); auto.
            discriminate.
          }
        * inv H3; reflexivity.

      + (* redirectExe *)
        kinv_action_dest.
        kinv_red; kregmap_red.
        kinvert_det; kinv_action_dest.
        destruct H.
        kinv_red; kregmap_red; kinv_red.

        exists (Some "killFetch").
        kinv_constr_det; kinv_eq_light; auto.
        
        inv H15; apply getArchPc_exe_redirected; auto.

      + (* redirectDec *)
        kinv_action_dest.
        kinv_red; kregmap_red.
        kinvert_det; kinv_action_dest.
        destruct H.
        kinv_red; kregmap_red; kinv_red.

        exists (Some "killFetch").
        kinv_constr_det; kinv_eq_light; auto.

        inv H3; apply getArchPc_dec_redirected; auto.

      + (* doIMem *)
        kinv_action_dest.
        kinv_red; kregmap_red.
        kinvert_det; kinv_action_dest.
        destruct H.
        kinv_red; kregmap_red; kinv_red.

        exists (Some "doIMem").
        kinv_constr_det; kinv_eq_light; auto.

        * destruct x12; try discriminate.
          reflexivity.
        * inv H3; reflexivity.
        * destruct x12 as [|f2id ?]; try discriminate.
          inv H3; inv H13; apply getArchPc_iMem_pass; auto.
        * inv H3; inv H13; reflexivity.

      + (* killDecode *)
        kinv_action_dest.
        kinv_red; kregmap_red.
        kinvert_det; kinv_action_dest.
        destruct H.
        kinv_red; kregmap_red; kinv_red.

        exists (Some "killDecode").
        kinv_constr_det; kinv_eq_light; auto.
        * destruct x9; try discriminate.
          reflexivity.
        * destruct x9; try discriminate.
          inv H3; inv H13; apply getArchPc_decode_killed; auto.
          unfold i2dValid.
          destruct x0, x10, (t Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))),
          (t Fin.F1 (Fin.FS (Fin.FS Fin.F1))); try discriminate; auto.

      + (* doDecode *)
        admit.
      + (* doRegRead *)
        admit.
      + (* killExecute *)
        admit.
      + (* doExecute *)
        admit.
        
  Admitted.
  
End Processor.


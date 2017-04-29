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

  Lemma getArchPcD2R_app:
    forall exeEpochv (d2rv1 d2rv2: list (type (Struct D2R))),
      getArchPcD2R exeEpochv (d2rv1 ++ d2rv2) =
      match getArchPcD2R exeEpochv d2rv1 with
      | Some v => Some v
      | None => getArchPcD2R exeEpochv d2rv2
      end.
  Proof.
    induction d2rv1; intros; auto.
    simpl.
    destruct (d2rValid exeEpochv a); auto.
  Qed.

  Fixpoint getArchPcR2E (exeEpoch: bool) (r2e: list (type (Struct R2E)))
    : option (fullType type (SyntaxKind (Bit addrSize))) :=
    match r2e with
    | nil => None
    | e :: r2e' =>
      if r2eValid exeEpoch e
      then Some (e Fin.F1)
      else getArchPcR2E exeEpoch r2e'
    end.

  Lemma getArchPcR2E_app:
    forall exeEpochv (r2ev1 r2ev2: list (type (Struct R2E))),
      getArchPcR2E exeEpochv (r2ev1 ++ r2ev2) =
      match getArchPcR2E exeEpochv r2ev1 with
      | Some v => Some v
      | None => getArchPcR2E exeEpochv r2ev2
      end.
  Proof.
    induction r2ev1; intros; auto.
    simpl.
    destruct (r2eValid exeEpochv a); auto.
  Qed.

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

  Lemma consistentExeEpochF2I_invalid:
    forall decEpochv exeEpochv f2iv,
      consistentExeEpochF2I (negb exeEpochv) f2iv ->
      getArchPcF2I decEpochv exeEpochv f2iv = None.
  Proof.
    induction f2iv; simpl; intros; auto.
    inv H.
    unfold f2iValid.
    replace (eqb (a Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) exeEpochv) with false
      by (destruct (a Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))), exeEpochv; auto).
    rewrite andb_false_r.
    auto.
  Qed.

  Lemma consistentExeEpochI2D_invalid:
    forall decEpochv exeEpochv i2dv,
      consistentExeEpochI2D (negb exeEpochv) i2dv ->
      getArchPcI2D decEpochv exeEpochv i2dv = None.
  Proof.
    induction i2dv; simpl; intros; auto.
    inv H.
    unfold i2dValid.
    replace (eqb (a Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) exeEpochv) with false
      by (destruct (a Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))), exeEpochv; auto).
    rewrite andb_false_r.
    auto.
  Qed.

  Lemma consistentExeEpochD2R_invalid:
    forall exeEpochv d2rv,
      consistentExeEpochD2R (negb exeEpochv) d2rv ->
      getArchPcD2R exeEpochv d2rv = None.
  Proof.
    induction d2rv; simpl; intros; auto.
    inv H.
    unfold d2rValid.
    replace (eqb (a (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) exeEpochv) with false
      by (destruct (a (Fin.FS (Fin.FS (Fin.FS Fin.F1)))), exeEpochv; auto).
    auto.
  Qed.

  Lemma consistentExeEpochR2E_invalid:
    forall exeEpochv r2ev,
      consistentExeEpochR2E (negb exeEpochv) r2ev ->
      getArchPcR2E exeEpochv r2ev = None.
  Proof.
    induction r2ev; simpl; intros; auto.
    inv H.
    unfold r2eValid.
    replace (eqb (a (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))) exeEpochv) with false
      by (destruct (a (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))), exeEpochv; auto).
    auto.
  Qed.

  Lemma getArchPc_exe_redirected:
    forall pcv decEpochv exeEpochv f2iv i2dv d2rv r2ev
           (decRedirv exeRedirv decRedirv' exeRedirv'
            : fullType type (SyntaxKind (RedirectK addrSize))),
      consistentExeEpoch (negb exeEpochv) f2iv i2dv d2rv r2ev ->
      exeRedirv Fin.F1 = true ->
      exeRedirv' Fin.F1 = false -> decRedirv' Fin.F1 = false ->
      getArchPc pcv decEpochv exeEpochv decRedirv exeRedirv f2iv i2dv d2rv r2ev =
      getArchPc (exeRedirv (Fin.FS Fin.F1) (Fin.FS Fin.F1)) decEpochv exeEpochv
                decRedirv' exeRedirv' f2iv i2dv d2rv r2ev.
  Proof.
    unfold consistentExeEpoch, getArchPc; intros; dest.
    rewrite consistentExeEpochR2E_invalid by assumption.
    rewrite consistentExeEpochD2R_invalid by assumption.
    rewrite consistentExeEpochI2D_invalid by assumption.
    rewrite consistentExeEpochF2I_invalid by assumption.
    simpl.
    unfold getPcRedir, maybeToOption.
    rewrite H0, H1, H2; simpl.
    reflexivity.
  Qed.

  Lemma consistentDecEpochF2I_invalid:
    forall decEpochv exeEpochv f2iv,
      consistentDecEpochF2I (negb decEpochv) f2iv ->
      getArchPcF2I decEpochv exeEpochv f2iv = None.
  Proof.
    induction f2iv; simpl; intros; auto.
    inv H.
    unfold f2iValid.
    replace (eqb (a Fin.F1 (Fin.FS (Fin.FS Fin.F1))) decEpochv) with false
      by (destruct (a Fin.F1 (Fin.FS (Fin.FS Fin.F1))), decEpochv; auto).
    auto.
  Qed.

  Lemma consistentDecEpochI2D_invalid:
    forall decEpochv exeEpochv i2dv,
      consistentDecEpochI2D (negb decEpochv) i2dv ->
      getArchPcI2D decEpochv exeEpochv i2dv = None.
  Proof.
    induction i2dv; simpl; intros; auto.
    inv H.
    unfold i2dValid.
    replace (eqb (a Fin.F1 (Fin.FS (Fin.FS Fin.F1))) decEpochv) with false
      by (destruct (a Fin.F1 (Fin.FS (Fin.FS Fin.F1))), decEpochv; auto).
    auto.
  Qed.

  Lemma getArchPc_dec_redirected:
    forall pcv decEpochv exeEpochv f2iv i2dv d2rv r2ev
           (decRedirv exeRedirv decRedirv': fullType type (SyntaxKind (RedirectK addrSize))),
      consistentDecEpoch (negb decEpochv) f2iv i2dv ->
      decRedirv Fin.F1 = true ->
      decRedirv' Fin.F1 = false ->
      getArchPc pcv decEpochv exeEpochv decRedirv exeRedirv f2iv i2dv d2rv r2ev =
      getArchPc (decRedirv (Fin.FS Fin.F1) (Fin.FS Fin.F1)) decEpochv exeEpochv
                decRedirv' exeRedirv f2iv i2dv d2rv r2ev.
  Proof.
    unfold consistentDecEpoch, getArchPc; intros; dest.
    rewrite consistentDecEpochI2D_invalid by assumption.
    rewrite consistentDecEpochF2I_invalid by assumption.
    simpl.
    unfold getPcRedir, maybeToOption.
    rewrite H0, H1; simpl.
    reflexivity.
  Qed.

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

  Lemma getArchPc_decode_pass:
    forall pcv decEpochv decEpochv' exeEpochv
           (decRedirv decRedirv' exeRedirv: fullType type (SyntaxKind (RedirectK addrSize)))
           f2iv i2dv (i2de: fullType type (SyntaxKind (Struct I2D)))
           d2rv (d2re: fullType type (SyntaxKind (Struct D2R))) r2ev,
      i2dValid decEpochv exeEpochv i2de = true ->
      d2rValid exeEpochv d2re = true ->
      i2de Fin.F1 Fin.F1 = d2re Fin.F1 ->
      decRedirv Fin.F1 = false ->
      getArchPc pcv decEpochv exeEpochv decRedirv exeRedirv f2iv (i2de :: i2dv) d2rv r2ev =
      getArchPc pcv decEpochv' exeEpochv decRedirv' exeRedirv f2iv i2dv (d2rv ++ [d2re]) r2ev.
  Proof.
    unfold getArchPc; intros.
    rewrite getArchPcD2R_app; simpl.
    rewrite H, H0; simpl.
    rewrite H1.
    destruct (getPcRedir exeRedirv); auto; simpl.
    destruct (getArchPcR2E exeEpochv r2ev); auto; simpl.
    destruct (getArchPcD2R exeEpochv d2rv); auto; simpl.
    unfold getPcRedir, maybeToOption; rewrite H2.
    reflexivity.
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

  Lemma getArchPc_regRead_pass:
    forall pcv decEpochv exeEpochv decRedirv exeRedirv
           f2iv i2dv d2rv (d2re: fullType type (SyntaxKind (Struct D2R)))
           r2ev (r2ee: fullType type (SyntaxKind (Struct R2E))),
      d2re Fin.F1 = r2ee Fin.F1 ->
      d2re (Fin.FS (Fin.FS (Fin.FS Fin.F1))) =
      r2ee (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))) ->
      getArchPc pcv decEpochv exeEpochv decRedirv exeRedirv f2iv i2dv (d2re :: d2rv) r2ev =
      getArchPc pcv decEpochv exeEpochv decRedirv exeRedirv f2iv i2dv d2rv (r2ev ++ [r2ee]).
  Proof.
    unfold getArchPc; intros.
    rewrite getArchPcR2E_app; simpl.
    unfold d2rValid, r2eValid.
    rewrite H, H0.
    destruct (getArchPcR2E exeEpochv r2ev); auto; simpl.
    destruct (eqb _ _); auto.
  Qed.

  Lemma getArchPc_execute_killed:
    forall pcv decEpochv exeEpochv decRedirv exeRedirv
           f2iv i2dv d2rv r2ev
           (r2ee: fullType type (SyntaxKind (Struct R2E))),
      r2eValid exeEpochv r2ee = false ->
      getArchPc pcv decEpochv exeEpochv decRedirv exeRedirv f2iv i2dv d2rv (r2ee :: r2ev) =
      getArchPc pcv decEpochv exeEpochv decRedirv exeRedirv f2iv i2dv d2rv r2ev.
  Proof.
    unfold getArchPc; intros.
    simpl; rewrite H; reflexivity.
  Qed.

  Lemma getArchPc_execute_valid:
    forall pcv decEpochv exeEpochv
           (decRedirv exeRedirv: fullType type (SyntaxKind (RedirectK addrSize)))
           f2iv i2dv d2rv r2ev
           (r2ee: fullType type (SyntaxKind (Struct R2E))),
      exeRedirv Fin.F1 = false ->
      r2eValid exeEpochv r2ee = true ->
      getArchPc pcv decEpochv exeEpochv decRedirv exeRedirv f2iv i2dv d2rv (r2ee :: r2ev) =
      r2ee Fin.F1.
  Proof.
    unfold getArchPc, getPcRedir, maybeToOption; intros; simpl.
    rewrite H, H0; simpl; reflexivity.
  Qed.

  Lemma getArchPc_execute_valid_post:
    forall pcv decEpochv exeEpochv
           (decRedirv exeRedirv: fullType type (SyntaxKind (RedirectK addrSize)))
           f2iv i2dv d2rv r2ev
           (r2ee: fullType type (SyntaxKind (Struct R2E))),
      exeRedirv Fin.F1 = false ->
      r2eValid exeEpochv r2ee = true ->
      consistentExeEpoch exeEpochv f2iv i2dv d2rv (r2ee :: r2ev) ->
      ((decRedirv Fin.F1 = false /\
        pcChainFromPc pcv decEpochv exeEpochv f2iv i2dv d2rv (r2ee :: r2ev)) \/
       (decRedirv Fin.F1 = true /\
        pcChainFromDec (decRedirv (Fin.FS Fin.F1) (Fin.FS Fin.F1))
                       exeEpochv d2rv (r2ee :: r2ev))) ->
      getArchPc pcv decEpochv exeEpochv decRedirv exeRedirv f2iv i2dv d2rv r2ev =
      r2ee (Fin.FS Fin.F1).
  Proof.
    intros; destruct H2; dest.
    - unfold consistentExeEpoch in H1; dest.
      unfold pcChainFromPc in H3; simpl in H3.
  Admitted.

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
        kinv_action_dest.
        * (* case redirected *)
          kinv_red; kregmap_red.
          kinvert_det; kinv_action_dest.
          destruct H.
          kinv_red; kregmap_red; kinv_red.

          destruct x13 as [|i2de ?]; try discriminate.
          inv H3; inv H13; inv H15; inv H20.

          exists (Some "doDecode").
          kinv_constr_det; kinv_eq_light; auto.
          { kinv_finish. }
          { apply getArchPc_decode_pass; auto.
            { unfold i2dValid.
              rewrite 2! eqb_reflx; reflexivity.
            }
            { unfold d2rValid; simpl.
              rewrite eqb_reflx; reflexivity.
            }
          }
          
        * (* case not redirected *)
          kinv_red; kregmap_red.
          kinvert_det; kinv_action_dest.
          destruct H.
          kinv_red; kregmap_red; kinv_red.

          destruct x11 as [|i2de ?]; try discriminate.
          inv H3; inv H13; inv H15.

          exists (Some "doDecode").
          kinv_constr_det; kinv_eq_light; auto.
          { kinv_finish. }
          { apply getArchPc_decode_pass; auto.
            { unfold i2dValid.
              rewrite 2! eqb_reflx; reflexivity.
            }
            { unfold d2rValid; simpl.
              rewrite eqb_reflx; reflexivity.
            }
            { destruct (x2 Fin.F1); auto.
              specialize (HdrSpec eq_refl).
              inv HdrSpec.
              inv H1.
              exfalso; eapply negb_eq_false; eauto.
            }
          }

      + (* doRegRead *)
        kinv_action_dest.
        kinv_red; kregmap_red.
        kinvert_det; kinv_action_dest.
        destruct H.
        kinv_red; kregmap_red; kinv_red.

        destruct x15 as [|d2re ?]; try discriminate.
        inv H3; inv H13.

        exists (Some "doRegRead").
        kinv_constr_det; kinv_eq_light; auto.
        * kinv_finish.
        * kinv_finish.
        * apply getArchPc_regRead_pass; auto.

      + (* killExecute *)
        kinv_action_dest.
        kinv_red; kregmap_red.
        kinvert_det; kinv_action_dest.
        destruct H.
        kinv_red; kregmap_red; kinv_red.

        exists (Some "killExecute").
        kinv_constr_det; kinv_eq_light; auto.
        * destruct x12; try discriminate.
          reflexivity.
        * destruct x12; try discriminate.
          inv H3; inv H13; apply getArchPc_execute_killed; auto.
          unfold r2eValid.
          apply eqb_false_iff; auto.

      + (* doExecute *)
        kinv_action_dest.

        * (* case redirected *)
          kinv_red; kregmap_red.
          kinvert_det; kinv_action_dest.
          destruct H.
          kinv_red; kregmap_red; kinv_red.

          destruct x16 as [|r2ee ?]; try discriminate.
          inv H3; inv H13; inv H17; inv H20.

          exists (Some "doExecute").
          kinv_constr_det; kinv_eq_light; auto.

          simpl; destruct (weq _ _); auto.
          elim n; clear n.
          apply eq_sym, getArchPc_execute_valid; auto.
          unfold r2eValid; simpl.
          rewrite eqb_reflx; reflexivity.

        * (* case redirected *)
          kinv_red; kregmap_red.
          kinvert_det; kinv_action_dest.
          destruct H.
          kinv_red; kregmap_red; kinv_red.

          destruct x11 as [|r2ee ?]; try discriminate.
          inv H3; inv H13.

          exists (Some "doExecute").
          kinv_constr_det; kinv_eq_light; auto.
          { simpl; destruct (weq _ _); auto.
            elim n; clear n.
            apply eq_sym, getArchPc_execute_valid; auto.
            { destruct (x3 Fin.F1); auto.
              specialize (HerSpec eq_refl).
              unfold consistentExeEpoch in HerSpec; dest.
              inv H3.
              exfalso; eapply negb_eq_false; eauto.
            }
            { unfold r2eValid; simpl.
              rewrite eqb_reflx; reflexivity.
            }
          }
          { (* TODO: should be able to prove the below replacement by requiring
             * more assumptions to AbstractIsa.execInst
             *)
            replace
              (evalExpr
                 (execInst type (r2ee (Fin.FS (Fin.FS Fin.F1)))
                           (r2ee (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
                           (r2ee (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1))))) (r2ee Fin.F1) 
                           (r2ee (Fin.FS Fin.F1))) (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))
            with (r2ee (Fin.FS Fin.F1)) by admit.

            (* exeRedir should be empty *)
            assert (x3 Fin.F1 = false) by admit.

            apply eq_sym, getArchPc_execute_valid_post; auto.
            { unfold r2eValid.
              rewrite eqb_reflx; reflexivity.
            }
            { destruct (x2 Fin.F1).
              { right; repeat split; auto. }
              { left; repeat split; auto. }
            }
          }
  Admitted.
  
End Processor.


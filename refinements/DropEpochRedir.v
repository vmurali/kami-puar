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
  Definition e2m := e2m addrSize dataBytes rfIdx.

  (** Mem related *)
  Definition mem := mem addrSize dataBytes rfIdx.
  Definition m2d := m2d addrSize dataBytes rfIdx.

  (** DMem related *)
  Definition dMem := dMem addrSize dataBytes rfIdx.
  Definition d2w := d2w addrSize dataBytes rfIdx.

  (** Writeback related *)
  Definition writeback := writeback addrSize dataBytes rfIdx.

  Definition fidreComb := fidreComb decodeInst execInst.
  
  Definition fidreNR :=
    (fetchNondetNR ++ f2i
                   ++ iMem ++ i2d
                   ++ decodeNondetNR ++ d2r
                   ++ regRead ++ r2e
                   ++ executeNondetNR)%kami.

  Section RefinementNR.

    Definition F2I := F2I addrSize dataBytes.
    Definition I2D := I2D addrSize dataBytes.
    Definition D2R := D2R addrSize dataBytes rfIdx.
    Definition R2E := R2E addrSize dataBytes rfIdx.

    Fixpoint getArchPcF2I (decEpoch exeEpoch: bool) (f2i: list (type (Struct F2I)))
      : option (fullType type (SyntaxKind (Bit addrSize))) :=
      match f2i with
      | nil => None
      | e :: f2i' =>
        if (eqb (e Fin.F1 (Fin.FS (Fin.FS Fin.F1))) decEpoch &&
                eqb (e Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) exeEpoch)
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
      destruct ((eqb (a Fin.F1 (Fin.FS (Fin.FS Fin.F1))) decEpochv)
                  && (eqb (a Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) exeEpochv)); auto.
    Qed.

    Fixpoint getArchPcI2D (decEpoch exeEpoch: bool) (i2d: list (type (Struct I2D)))
      : option (fullType type (SyntaxKind (Bit addrSize))) :=
      match i2d with
      | nil => None
      | e :: i2d' =>
        if (eqb (e Fin.F1 (Fin.FS (Fin.FS Fin.F1))) decEpoch &&
                eqb (e Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) exeEpoch)
        then Some (e Fin.F1 Fin.F1)
        else getArchPcI2D decEpoch exeEpoch i2d'
      end.

    Fixpoint getArchPcD2R (exeEpoch: bool) (d2r: list (type (Struct D2R)))
      : option (fullType type (SyntaxKind (Bit addrSize))) :=
      match d2r with
      | nil => None
      | e :: d2r' =>
        if (eqb (e (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) exeEpoch)
        then Some (e Fin.F1)
        else getArchPcD2R exeEpoch d2r'
      end.

    Fixpoint getArchPcR2E (exeEpoch: bool) (r2e: list (type (Struct R2E)))
      : option (fullType type (SyntaxKind (Bit addrSize))) :=
      match r2e with
      | nil => None
      | e :: r2e' =>
        if (eqb (e (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))) exeEpoch)
        then Some (e Fin.F1)
        else getArchPcR2E exeEpoch r2e'
      end.

    Local Definition otake {A} (oa: option A) (default: A): A :=
      match oa with
      | Some a => a
      | None => default
      end.
    Infix ">>=" := otake (at level 0, right associativity).

    Definition getArchPc (pcv: fullType type (SyntaxKind (Bit addrSize)))
               (decEpoch exeEpoch: fullType type (SyntaxKind Bool))
               (f2i: fullType type (@NativeKind (list (type (Struct F2I))) nil))
               (i2d: fullType type (@NativeKind (list (type (Struct I2D))) nil))
               (d2r: fullType type (@NativeKind (list (type (Struct D2R))) nil))
               (r2e: fullType type (@NativeKind (list (type (Struct R2E))) nil)) :=
      (getArchPcR2E exeEpoch r2e)
        >>= (getArchPcD2R exeEpoch d2r)
        >>= (getArchPcI2D decEpoch exeEpoch i2d)
        >>= (getArchPcF2I decEpoch exeEpoch f2i)
        >>= pcv.

    Definition f2iValid (decEpoch exeEpoch: bool) (e: type (Struct F2I)) :=
      eqb (e Fin.F1 (Fin.FS (Fin.FS Fin.F1))) decEpoch &&
          eqb (e Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) exeEpoch.

    Definition f2iFilter (decEpoch exeEpoch: bool)
               (f2i: list (type (Struct F2I)))
      : fullType type (@NativeKind (list (type (Struct F2I))) nil) :=
      filter (f2iValid decEpoch exeEpoch) f2i.

    Definition i2dValid (decEpoch exeEpoch: bool) (e: type (Struct I2D)) :=
      eqb (e Fin.F1 (Fin.FS (Fin.FS Fin.F1))) decEpoch &&
          eqb (e Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) exeEpoch.

    Definition i2dFilter (decEpoch exeEpoch: bool)
               (i2d: list (type (Struct I2D)))
      : fullType type (@NativeKind (list (type (Struct I2D))) nil) :=
      filter (i2dValid decEpoch exeEpoch) i2d.

    Definition d2rValid (exeEpoch: bool) (e: type (Struct D2R)) :=
      eqb (e (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) exeEpoch.

    Definition d2rFilter (exeEpoch: bool)
               (d2r: list (type (Struct D2R)))
      : fullType type (@NativeKind (list (type (Struct D2R))) nil) :=
      filter (d2rValid exeEpoch) d2r.

    Definition r2eValid (exeEpoch: bool) (e: type (Struct R2E)) :=
      eqb (e (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))) exeEpoch.

    Definition r2eFilter (exeEpoch: bool)
               (r2e: list (type (Struct R2E)))
      : fullType type (@NativeKind (list (type (Struct R2E))) nil) :=
      filter (r2eValid exeEpoch) r2e.

    Local Definition thetaR (ir sr: RegsT): Prop.
    Proof.
      kexistnv "pc" pcv ir (SyntaxKind (Bit addrSize)).
      kexistnv "decEpoch" decEpochv ir (SyntaxKind Bool).
      kexistnv "exeEpoch" exeEpochv ir (SyntaxKind Bool).
      kexistnv (f2iName -- Names.elt) f2iv ir (@NativeKind (list (type (Struct F2I))) nil).
      kexistnv (i2dName -- Names.elt) i2dv ir (@NativeKind (list (type (Struct I2D))) nil).
      kexistnv (d2rName -- Names.elt) d2rv ir (@NativeKind (list (type (Struct D2R))) nil).
      kexistnv (r2eName -- Names.elt) r2ev ir (@NativeKind (list (type (Struct R2E))) nil).

      exact (sr =
             ["pc" <- existT _ _ pcv]
             +[(f2iName -- Names.elt) <- existT _ _ (f2iFilter decEpochv exeEpochv f2iv)]
             +[(i2dName -- Names.elt) <- existT _ _ (i2dFilter decEpochv exeEpochv i2dv)]
             +[(d2rName -- Names.elt) <- existT _ _ (d2rFilter exeEpochv d2rv)]
             +[(r2eName -- Names.elt) <- existT _ _ (r2eFilter exeEpochv r2ev)]
             +["archPc" <- existT _ _ (getArchPc pcv decEpochv exeEpochv
                                                 f2iv i2dv d2rv r2ev)])%fmap.
    Defined.

    Hint Unfold F2I I2D D2R R2E : MethDefs.
    Hint Unfold thetaR : InvDefs.

    (** Some utilities for [thetaR] preservation *)
    
    Definition f2i_enq_pc (pcv: fullType type (SyntaxKind (Bit addrSize)))
               (f2ie: type (Struct F2I)) :=
      f2ie Fin.F1 Fin.F1 = pcv.

    Lemma f2i_valid_enq_getArchPc_preserved:
      forall pcv decEpochv exeEpochv f2iv i2dv d2rv r2ev f2ie,
        f2iValid decEpochv exeEpochv f2ie = true ->
        f2i_enq_pc pcv f2ie ->
        forall pcv',
          getArchPc pcv decEpochv exeEpochv f2iv i2dv d2rv r2ev =
          getArchPc pcv' decEpochv exeEpochv (f2iv ++ [f2ie])%list i2dv d2rv r2ev.
    Proof.
      unfold f2iValid, f2i_enq_pc, getArchPc; intros.
      unfold otake.

      destruct (getArchPcR2E exeEpochv r2ev); auto.
      destruct (getArchPcD2R exeEpochv d2rv); auto.
      destruct (getArchPcI2D decEpochv exeEpochv i2dv); auto.

      rewrite getArchPcF2I_app.
      destruct (getArchPcF2I decEpochv exeEpochv f2iv); auto.
      simpl; rewrite H; auto.
    Qed.

    Lemma f2iFilter_app:
      forall decEpochv exeEpochv f2iv1 f2iv2,
        f2iFilter decEpochv exeEpochv (f2iv1 ++ f2iv2) =
        ((f2iFilter decEpochv exeEpochv f2iv1)
           ++ (f2iFilter decEpochv exeEpochv f2iv2))%list.
    Proof.
      intros; apply filter_app.
    Qed.

    Lemma f2iFilter_valid_consistent:
      forall decEpochv exeEpochv f2iv f2ie,
        f2iValid decEpochv exeEpochv f2ie = true ->
        NativeFifo.listEnq f2ie (f2iFilter decEpochv exeEpochv f2iv) =
        f2iFilter decEpochv exeEpochv (f2iv ++ [f2ie]).
    Proof.
      intros.
      rewrite f2iFilter_app.
      unfold NativeFifo.listEnq.
      f_equal.
      simpl; rewrite H; auto.
    Qed.

    Lemma f2iValid_invalid_f2iFilter:
      forall decEpochv exeEpochv f2iv f2ie,
        f2iValid decEpochv exeEpochv f2ie = false ->
        f2iFilter decEpochv exeEpochv f2iv =
        f2iFilter decEpochv exeEpochv (f2iv ++ [f2ie]).
    Proof.
      intros; rewrite f2iFilter_app; simpl.
      rewrite H, app_nil_r; reflexivity.
    Qed.

    Notation "'_STRUCT_'" := (fun i : Fin.t _ => _).
    Notation "'_STRUCT_SIG_'" := (forall i : Fin.t _, _).

    Lemma Attribute_inv:
      forall {A} (n1 n2: string) (v1 v2: A),
        ((n1 :: v1) = (n2 :: v2))%struct -> n1 = n2 /\ v1 = v2.
    Proof.
      intros; inv H; auto.
    Qed.

    Ltac kinvert_det :=
      repeat
        match goal with
        | [H: SubstepMeths _ _ _ _ |- _] => inv H
        | [H: Substep _ _ _ (Meth (Some _)) _ |- _] => inv H
        | [H: (_ :: _)%struct = (_ :: _)%struct |- _] =>
          apply Attribute_inv in H; destruct H; subst
        | [H1: In ?f (getDefsBodies _), H2: _ = Struct.attrName ?f |- _] =>
          let fn := fresh "fn" in
          let fa := fresh "fa" in
          destruct f as [fn fa]; simpl in *; subst;
          repeat
            match goal with
            | [H: _ \/ _ |- _] => destruct H; try discriminate
            | [H: False |- _] => elim H
            end
        (* Below inversion mechanism for [existT] should be at the end of this Ltac *)
        | [H: existT _ _ _ = existT _ _ _ |- _] => destruct_existT
        end.

    Ltac kinv_constr_det :=
      repeat
        match goal with
        | [ |- exists _, _ /\ _ ] => eexists; split
        | [ |- Step _ _ _ _ ] =>
          apply stepDet_implies_step; [kequiv|repeat (constructor || reflexivity)|]
        | [ |- StepDet _ _ _ _ ] => econstructor
        | [ |- SubstepMeths _ _ _ _ ] => econstructor
        | [ |- Substep _ _ _ _ _ ] => econstructor
        | [ |- In _ _ ] => simpl; tauto
        | [ |- SemAction _ _ _ _ _ ] => econstructor
        | [ |- _ = _ ] => reflexivity
        end.

    Theorem fidreComb_fidreNR: fidreComb <<== fidreNR.
    Proof.
      apply stepRefinementR with (thetaR:= thetaR).
      - kdecompose_regrel_init.
        meqReify.

      - intros.
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
          kinv_red; kregmap_red; kinv_red.

          case_eq (f2iValid x0 x1 argV); intros.
          * exists (Some "doFetch").
            kinv_constr_det; kinv_eq_light; auto.
            -- apply f2i_valid_enq_getArchPc_preserved; auto.
               inv H3; reflexivity.
            -- inv H3.
               apply f2iFilter_valid_consistent; auto.
          * exists (Some "killFetch").
            kinv_constr_det; kinv_eq_light; auto.
            -- admit. (* TODO: need an invariant saying that there exists 
                       * _a valid element_ in the fifos if we can find 
                       * an invalid element in the fifos.
                       *)
            -- apply f2iValid_invalid_f2iFilter; auto.

        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.
        + admit.

    Admitted.

  End RefinementNR.
  
End Processor.


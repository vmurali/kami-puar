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


(** Some utilities for [thetaR] preservation *)

Notation "'_STRUCT_'" := (fun i : Fin.t _ => _).
Notation "'_STRUCT_SIG_'" := (forall i : Fin.t _, _).

Lemma Attribute_inv:
  forall {A} (n1 n2: string) (v1 v2: A),
    ((n1 :: v1) = (n2 :: v2))%struct -> n1 = n2 /\ v1 = v2.
Proof.
  intros; inv H; auto.
Qed.

Ltac kinvert_det_unit :=
  match goal with
  | [H: SubstepMeths _ _ _ _ |- _] => inv H
  | [H: Substep _ _ _ (Meth (Some _)) _ |- _] => inv H
  | [H: (_ :: _)%struct = (_ :: _)%struct |- _] =>
    apply Attribute_inv in H; destruct H; subst
  | [H1: In ?f (getDefsBodies _), H2: _ = Struct.attrName ?f |- _] =>
    let fn := fresh "fn" in
    let fa := fresh "fa" in
    destruct f as [fn fa]; simpl in H1, H2; subst;
    repeat
      match goal with
      | [H: _ \/ _ |- _] => destruct H; try discriminate
      | [H: False |- _] => elim H
      end
  (* Below inversion mechanism for [existT] should be at the end of this Ltac *)
  | [H: existT _ _ _ = existT _ _ _ |- _] => destruct_existT
  end.

Ltac kinvert_det := repeat kinvert_det_unit.

Ltac kinv_constr_det_unit :=
  match goal with
  | [ |- exists _, _ /\ _ ] => eexists; split
  | [ |- Step _ _ _ _ ] =>
    apply stepDet_implies_step; [kequiv|repeat (constructor || reflexivity)|]
  | [ |- StepDet _ _ _ _ ] => econstructor
  | [ |- SubstepMeths _ _ _ _ ] => econstructor
  | [ |- Substep _ _ _ (Meth (Some (?fn :: _)%struct)) _ ] =>
    eapply SingleMeth with (f:= (fn :: _)%struct)
  | [ |- Substep _ _ _ _ _ ] => econstructor
  | [ |- In _ _ ] => simpl; tauto
  | [ |- SemAction _ _ _ _ _ ] => econstructor
  | [ |- _ = _ ] => reflexivity
  end.

Ltac kinv_constr_det := repeat kinv_constr_det_unit.

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

  Section Invariant.

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

    Lemma fidreComb_epoch_invariant_ok:
      forall o, reachable o fidreComb -> epoch_invariant o.
    Proof.
      (* intros; apply stepInv with (m:= fidreComb); auto. *)

      (* - econstructor; *)
      (*     try (findReify; (reflexivity || eassumption); fail); *)
      (*     auto. *)

      (* - clear H o; intros. *)

      (*   apply step_implies_stepDet in H0; *)
      (*     [|kequiv|repeat (constructor || reflexivity)|reflexivity]. *)
      (*   inv H0; simpl; try mred. *)

      (*   kinvert. *)

      (*   + (* doFetch *) *)
      (*     kinv_action_dest. *)
      (*     kinv_red; kregmap_red. *)
      (*     kinvert_det; kinv_action_dest. *)

      (*     destruct H. *)
      (*     kinv_red; kregmap_red; kinv_red. *)
      (*     econstructor; *)
      (*       try (findReify; try (reflexivity || eassumption); fail); *)
      (*       try assumption. *)

      (*   + (* redirectExe *) *)
      (*     kinv_action_dest. *)
      (*     kinv_red; kregmap_red. *)
      (*     kinvert_det; kinv_action_dest. *)

      (*     destruct H. *)
      (*     kinv_red; kregmap_red; kinv_red. *)
      (*     econstructor; *)
      (*       try (findReify; try (reflexivity || eassumption); fail); *)
      (*       try assumption. *)

      (*     * destruct (x5 Fin.F1); auto. *)
      (*     * inv H1. *)
      (*       destruct (x6 Fin.F1); auto. *)
      (*       destruct x0, decEpochv; auto. *)
      (*       specialize (HdeSpec1 eq_refl); discriminate. *)
      (*     * intros; reflexivity. *)
      (*     * inv H6; rewrite H4 in *. *)
      (*       destruct x2, exeEpochv; auto. *)
      (*       specialize (HeeSpec1 eq_refl); discriminate. *)
          
      (*   + (* redirectDec *) *)
      (*     kinv_action_dest. *)
      (*     kinv_red; kregmap_red. *)
      (*     kinvert_det; kinv_action_dest. *)

      (*     destruct H. *)
      (*     kinv_red; kregmap_red; kinv_red. *)
      (*     econstructor; *)
      (*       try (findReify; try (reflexivity || eassumption); fail); *)
      (*       try assumption. *)

      (*     * intros; reflexivity. *)
      (*     * inv H1; rewrite H6 in *. *)
      (*       destruct x3, decEpochv; auto. *)
      (*       specialize (HdeSpec1 eq_refl); discriminate. *)
          
      (*   + (* doIMem *) *)
      (*     kinv_action_dest. *)
      (*     kinv_red; kregmap_red. *)
      (*     kinvert_det; kinv_action_dest. *)

      (*     destruct H. *)
      (*     kinv_red; kregmap_red; kinv_red. *)
      (*     econstructor; *)
      (*       try (findReify; try (reflexivity || eassumption); fail); *)
      (*       try assumption. *)
          
      (*   + (* killDecode *) *)
      (*     kinv_action_dest. *)
      (*     kinv_red; kregmap_red. *)
      (*     kinvert_det; kinv_action_dest. *)

      (*     destruct H. *)
      (*     kinv_red; kregmap_red; kinv_red. *)
      (*     econstructor; *)
      (*       try (findReify; try (reflexivity || eassumption); fail); *)
      (*       try assumption. *)
          
      (*   + (* doDecode *) *)
      (*     kinv_action_dest; *)
      (*       kinv_red; kregmap_red; *)
      (*         kinvert_det; kinv_action_dest. *)
          
      (*     * destruct H. *)
      (*       kinv_red; kregmap_red; kinv_red. *)
      (*       econstructor; *)
      (*         try (findReify; try (reflexivity || eassumption); fail); *)
      (*         try assumption. *)
      (*       { specialize (HdeSpec2 e). *)
      (*         subst; intros. *)
      (*         exfalso; eapply no_fixpoint_negb; eauto. *)
      (*       } *)
      (*       { intros; discriminate. } *)

      (*     * destruct H. *)
      (*       kinv_red; kregmap_red; kinv_red. *)
      (*       econstructor; *)
      (*         try (findReify; try (reflexivity || eassumption); fail); *)
      (*         try assumption. *)

      (*   + (* doRegRead *) *)
      (*     kinv_action_dest; *)
      (*       kinv_red; kregmap_red; *)
      (*         kinvert_det; kinv_action_dest; *)
      (*           abstract (destruct H; *)
      (*                     kinv_red; kregmap_red; kinv_red; *)
      (*                     econstructor; *)
      (*                     try (findReify; try (reflexivity || eassumption); fail); *)
      (*                     try assumption). *)
          
      (*   + (* killExecute *) *)
      (*     kinv_action_dest. *)
      (*     kinv_red; kregmap_red. *)
      (*     kinvert_det; kinv_action_dest. *)

      (*     destruct H. *)
      (*     kinv_red; kregmap_red; kinv_red. *)
      (*     econstructor; *)
      (*       try (findReify; try (reflexivity || eassumption); fail); *)
      (*       try assumption. *)

      (*   + (* doExecute *) *)
      (*     kinv_action_dest; *)
      (*       kinv_red; kregmap_red; *)
      (*         kinvert_det; kinv_action_dest. *)
          
      (*     * destruct H. *)
      (*       kinv_red; kregmap_red; kinv_red. *)
      (*       econstructor; *)
      (*         try (findReify; try (reflexivity || eassumption); fail); *)
      (*         try assumption. *)
      (*       { specialize (HeeSpec2 e). *)
      (*         subst; intros. *)
      (*         exfalso; eapply no_fixpoint_negb; eauto. *)
      (*       } *)
      (*       { intros; discriminate. } *)

      (*     * destruct H. *)
      (*       kinv_red; kregmap_red; kinv_red. *)
      (*       econstructor; *)
      (*         try (findReify; try (reflexivity || eassumption); fail); *)
      (*         try assumption. *)
    Admitted.

  End Invariant.
  
  Section RefinementNR.

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
        >>= (getPcRedir decRedir)
        >>= (getArchPcR2E exeEpoch r2e)
        >>= (getArchPcD2R exeEpoch d2r)
        >>= (getArchPcI2D decEpoch exeEpoch i2d)
        >>= (getArchPcF2I decEpoch exeEpoch f2i)
        >>= pcv.

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
          * admit. (* INVARIANT:
                    * - fetchEpochD = decEpoch <-> redirDec = None
                    * - fetchEpochE = exeEpoch <-> redirExe = None
                    *)
          * inv H3; reflexivity.

        + (* redirectExe *)
          kinv_action_dest.
          kinv_red; kregmap_red.
          kinvert_det; kinv_action_dest.
          kinv_red; kregmap_red; kinv_red.

          exists (Some "killFetch").
          kinv_constr_det; kinv_eq_light; auto.

          admit. (* INVARIANT: at this time, all elements in fifos are invalid
                  * in terms of two epoch comparisons
                  *)

        + (* redirectDec *)
          kinv_action_dest.
          kinv_red; kregmap_red.
          kinvert_det; kinv_action_dest.
          kinv_red; kregmap_red; kinv_red.

          exists (Some "killFetch").
          kinv_constr_det; kinv_eq_light; auto.

          admit. (* INVARIANT: at this time, all elements in fifos are invalid
                  * in terms of two epoch comparisons
                  *)

        + (* doIMem *)
          kinv_action_dest.
          kinv_red; kregmap_red.
          kinvert_det; kinv_action_dest.
          kinv_red; kregmap_red; kinv_red.

          exists (Some "doIMem").
          kinv_constr_det; kinv_eq_light; auto.

          * destruct x12; try discriminate.
            reflexivity.
          * inv H3; reflexivity.
          * admit. (* TODO: [getArchPc] consistency *)
          * inv H3; inv H13; reflexivity.

        + (* killDecode *)
          kinv_action_dest.
          kinv_red; kregmap_red.
          kinvert_det; kinv_action_dest.
          kinv_red; kregmap_red; kinv_red.

          exists (Some "killDecode").
          kinv_constr_det; kinv_eq_light; auto.
          * destruct x9; try discriminate.
            reflexivity.
          * admit. (* TODO: [getArchPc] consistency *)

        + (* doDecode *)
          admit. (* TODO: need to deal with "If" in [doDecode] *)
        + admit.
        + admit.
        + admit.
            
    Admitted.

  End RefinementNR.
  
End Processor.


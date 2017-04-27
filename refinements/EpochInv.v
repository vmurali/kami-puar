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
               consistentExeEpoch (negb exeEpochv) f2iv i2dv d2rv r2ev
    }.

  Local Notation "'_STRUCT_'" := (fun i : Fin.t _ => _).
  Local Notation "'_STRUCT_SIG_'" := (forall i : Fin.t _, _).

  Lemma fidreComb_epoch_invariant_ok:
    forall o, reachable o fidreComb -> epoch_invariant o.
  Proof.
    (* intros; apply stepInv with (m:= fidreComb); auto; *)
    (*   [econstructor; *)
    (*    try (findReify; (reflexivity || eassumption); fail); *)
    (*    auto; try (intros; inv H0)|]. *)

    (* clear H o; intros. *)
    (* apply step_implies_stepDet in H0; *)
    (*   [|kequiv|repeat (constructor || reflexivity)|reflexivity]. *)
    (* inv H0; simpl; try mred. *)

    (* kinvert. *)

    (* - (* doFetch *) *)
    (*   kinv_action_dest. *)
    (*   kinv_red; kregmap_red. *)
    (*   kinvert_det; kinv_action_dest. *)
    (*   destruct H. *)
    (*   kinv_red; kregmap_red; kinv_red. *)
      
    (*   econstructor; *)
    (*     try (findReify; try (reflexivity || eassumption); fail); *)
    (*     try assumption. *)
    (*   + admit. *)
    (*   + admit. *)

    (* - (* redirectExe *) *)
    (*   kinv_action_dest. *)
    (*   kinv_red; kregmap_red. *)
    (*   kinvert_det; kinv_action_dest. *)
    (*   destruct H. *)
    (*   kinv_red; kregmap_red; kinv_red. *)
      
    (*   econstructor; *)
    (*     try (findReify; try (reflexivity || eassumption); fail); *)
    (*     try assumption. *)

    (*   + destruct (x5 Fin.F1); auto. *)
    (*   + inv H1. *)
    (*     destruct (x6 Fin.F1); auto. *)
    (*     destruct x0, decEpochv; auto. *)
    (*     specialize (HdeSpec1 eq_refl); discriminate. *)
    (*   + intros; reflexivity. *)
    (*   + inv H6; rewrite H4 in *. *)
    (*     destruct x2, exeEpochv; auto. *)
    (*     specialize (HeeSpec1 eq_refl); discriminate. *)
    (*   + intros; inv H. *)
    (*   + intros; inv H. *)
        
    (* - (* redirectDec *) *)
    (*   kinv_action_dest. *)
    (*   kinv_red; kregmap_red. *)
    (*   kinvert_det; kinv_action_dest. *)
    (*   destruct H. *)
    (*   kinv_red; kregmap_red; kinv_red. *)
      
    (*   econstructor; *)
    (*     try (findReify; try (reflexivity || eassumption); fail); *)
    (*     try assumption. *)

    (*   + intros; reflexivity. *)
    (*   + inv H1; rewrite H6 in *. *)
    (*     destruct x3, decEpochv; auto. *)
    (*     specialize (HdeSpec1 eq_refl); discriminate. *)
    (*   + intros; inv H. *)
        
    (* - (* doIMem *) *)
    (*   kinv_action_dest. *)
    (*   kinv_red; kregmap_red. *)
    (*   kinvert_det; kinv_action_dest. *)
    (*   destruct H. *)
    (*   kinv_red; kregmap_red; kinv_red. *)
      
    (*   econstructor; *)
    (*     try (findReify; try (reflexivity || eassumption); fail); *)
    (*     try assumption. *)
    (*   + admit. *)
    (*   + admit. *)
      
    (* - (* killDecode *) *)
    (*   kinv_action_dest. *)
    (*   kinv_red; kregmap_red. *)
    (*   kinvert_det; kinv_action_dest. *)
    (*   destruct H. *)
    (*   kinv_red; kregmap_red; kinv_red. *)
      
    (*   econstructor; *)
    (*     try (findReify; try (reflexivity || eassumption); fail); *)
    (*     try assumption. *)
    (*   + admit. *)
    (*   + admit. *)
      
    (* - (* doDecode *) *)
    (*   kinv_action_dest; *)
    (*     kinv_red; kregmap_red; *)
    (*       kinvert_det; kinv_action_dest. *)
      
    (*   + destruct H. *)
    (*     kinv_red; kregmap_red; kinv_red. *)
    (*     econstructor; *)
    (*       try (findReify; try (reflexivity || eassumption); fail); *)
    (*       try assumption. *)
    (*     * specialize (HdeSpec2 e). *)
    (*       subst; intros. *)
    (*       exfalso; eapply no_fixpoint_negb; eauto. *)
    (*     * intros; discriminate. *)
    (*     * admit. *)
    (*     * admit. *)

    (*   + destruct H. *)
    (*     kinv_red; kregmap_red; kinv_red. *)
    (*     econstructor; *)
    (*       try (findReify; try (reflexivity || eassumption); fail); *)
    (*       try assumption. *)
    (*     * admit. *)
    (*     * admit. *)

    (* - (* doRegRead *) *)
    (*   kinv_action_dest; *)
    (*     kinv_red; kregmap_red; *)
    (*       kinvert_det; kinv_action_dest; *)
    (*         abstract (destruct H; *)
    (*                   kinv_red; kregmap_red; kinv_red; *)
    (*                   econstructor; *)
    (*                   try (findReify; try (reflexivity || eassumption); fail); *)
    (*                   try assumption; *)
    (*                   admit). *)
      
    (* - (* killExecute *) *)
    (*   kinv_action_dest. *)
    (*   kinv_red; kregmap_red. *)
    (*   kinvert_det; kinv_action_dest. *)

    (*   destruct H. *)
    (*   kinv_red; kregmap_red; kinv_red. *)
    (*   econstructor; *)
    (*     try (findReify; try (reflexivity || eassumption); fail); *)
    (*     try assumption. *)
    (*   + admit. *)
    (*   + admit. *)

    (* - (* doExecute *) *)
    (*   kinv_action_dest; *)
    (*     kinv_red; kregmap_red; *)
    (*       kinvert_det; kinv_action_dest. *)
      
    (*   + destruct H. *)
    (*     kinv_red; kregmap_red; kinv_red. *)
    (*     econstructor; *)
    (*       try (findReify; try (reflexivity || eassumption); fail); *)
    (*       try assumption. *)
    (*     * specialize (HeeSpec2 e). *)
    (*       subst; intros. *)
    (*       exfalso; eapply no_fixpoint_negb; eauto. *)
    (*     * intros; discriminate. *)
    (*     * admit. *)
    (*     * admit. *)

    (*   + destruct H. *)
    (*     kinv_red; kregmap_red; kinv_red. *)
    (*     econstructor; *)
    (*       try (findReify; try (reflexivity || eassumption); fail); *)
    (*       try assumption. *)
    (*     * admit. *)
    (*     * admit. *)
  Admitted.
  
End Processor.


Require Import Kami.
Require Import Lib.Indexer Lib.Struct Lib.FMap Lib.Reflection.
Require Import Kami.Tactics Kami.SemFacts Kami.StepDet.
Require Import Puar.Useful FunctionalExtensionality.

Require Import Eqdep.

Set Implicit Arguments.
Open Scope string.

(* Below implements a radix-4 Booth Multiplier.
 *
 * Note that the Booth multiplication algorithm is naturally designed
 * for signed integers, so we need to add sign bits (0) for unsigned integers
 * and their multiplication. It means we have to deal with 65 bits for 64-bit
 * unsigned multiplication.
 *
 * Here we assume the multiplier always takes _65-bit signed integers_ as
 * arguments.
 *)
Section Multiplier64.
  (* NOTE: it's hard to declare [LogNumPhases] and [NumBitsPerPhase] as 
   * variables, since truncation and extension require certain equation 
   * w.r.t. bit-lengths.
   *)
  (* Variable MultLogNumPhases MultNumStepsPerPhase: nat. *)
  Definition MultLogNumPhases := 3.
  Definition MultNumStepsPerPhase := 4.
  (* 2*4 = 8 bits are calculated per a phase. *)
  Definition MultNumBitsPerPhase := 2 * MultNumStepsPerPhase. 

  Definition MultNumPhases := wordToNat (wones MultLogNumPhases) + 1. (* 2^3 = 8 *)
  Definition MultNumBits := MultNumPhases * MultNumBitsPerPhase. (* 8*8 = 64 *)
  Definition MultNumBitsExt := MultNumBits + 1. (* 8*8 + 1 = 65 *)
  Definition MultBits := 2 * MultNumBitsExt + 2.

  Definition MultInStr := STRUCT { "multiplicand" :: Bit MultNumBitsExt;
                                   "multiplier" :: Bit MultNumBitsExt }.
  Definition MultOutStr := STRUCT { "high" :: Bit MultNumBits;
                                    "low" :: Bit MultNumBits }.

  Definition multRegister := MethodSig "multRegister"(Struct MultInStr): Void.
  Definition multGetResult := MethodSig "multGetResult"(Void): Struct MultOutStr.

  Definition boothStep' {ty}
             (m_pos m_neg: fullType ty (SyntaxKind (Bit MultBits)))
             (p: Expr ty (SyntaxKind (Bit MultBits)))
             (pr: Expr ty (SyntaxKind (Bit 2))) :=
    (IF (pr == $$(WO~0~1)) then p + #m_pos
     else IF (pr == $$(WO~1~0)) then p + #m_neg
     else p)%kami_expr.

  (* NOTE: must use shirt-right-arithmetic to preserve the sign bit. *)
  Definition boothStep {ty}
             (m_pos m_neg: fullType ty (SyntaxKind (Bit MultBits)))
             (p: Expr ty (SyntaxKind (Bit ((MultBits - 2) + 2))))
    : Expr ty (SyntaxKind (Bit MultBits)) :=
    ((boothStep' m_pos m_neg p (UniBit (Trunc 2 _) p)) ~>> $$(WO~1))%kami_expr.

  Lemma boothStep'_eval:
    forall m_pos m_neg p pr,
      evalExpr (boothStep' m_pos m_neg p pr) =
      if weq (evalExpr pr) WO~0~1 then evalExpr p ^+ m_pos
      else if weq (evalExpr pr) WO~1~0 then evalExpr p ^+ m_neg
           else evalExpr p.
  Proof.
    intros; simpl.
    destruct (weq _ _); try reflexivity.
    destruct (weq _ _); reflexivity.
  Qed.

  Lemma boothStep_eval:
    forall m_pos m_neg p,
      evalExpr (boothStep m_pos m_neg p) =
      if weq (split1 2 (MultBits - 2) (evalExpr p)) WO~0~1
      then sra (evalExpr p ^+ m_pos) 1
      else if weq (split1 2 (MultBits - 2) (evalExpr p)) WO~1~0
           then sra (evalExpr p ^+ m_neg) 1
           else sra (evalExpr p) 1.
  Proof.
    intros; unfold boothStep.
    unfold evalExpr; fold evalExpr.
    unfold evalBinBit.
    rewrite boothStep'_eval.

    destruct (weq _ _); [reflexivity|].
    destruct (weq _ _); reflexivity.
  Qed.

  Definition booth4Step' {ty}
             (m_pos m_neg: fullType ty (SyntaxKind (Bit MultBits)))
             (p: Expr ty (SyntaxKind (Bit MultBits)))
             (pr: Expr ty (SyntaxKind (Bit 3))) :=
    (IF (pr == $$(WO~0~0~1)) then p + #m_pos
     else IF (pr == $$(WO~0~1~0)) then p + #m_pos
     else IF (pr == $$(WO~0~1~1)) then p + (#m_pos << $$(WO~1))
     else IF (pr == $$(WO~1~0~0)) then p + (#m_neg << $$(WO~1))
     else IF (pr == $$(WO~1~0~1)) then p + #m_neg
     else IF (pr == $$(WO~1~1~0)) then p + #m_neg
     else p)%kami_expr.

  (* NOTE: must use shirt-right-arithmetic to preserve the sign bit. *)
  Definition booth4Step {ty}
             (m_pos m_neg: fullType ty (SyntaxKind (Bit MultBits)))
             (p: Expr ty (SyntaxKind (Bit ((MultBits - 3) + 3))))
    : Expr ty (SyntaxKind (Bit MultBits)) :=
    (booth4Step' m_pos m_neg p (UniBit (Trunc 3 _) p) ~>> $$(WO~1~0))%kami_expr.

  Fixpoint booth4Steps (cnt: nat)
           {ty} (m_pos m_neg: fullType ty (SyntaxKind (Bit MultBits)))
           (p: fullType ty (SyntaxKind (Bit ((MultBits - 3) + 3))))
           (cont: fullType ty (SyntaxKind (Bit ((MultBits - 3) + 3))) ->
                  ActionT ty Void)
    : ActionT ty Void :=
    match cnt with
    | O => (cont p)%kami_action
    | S n => (LET np <- booth4Step m_pos m_neg #p;
              booth4Steps n m_pos m_neg np cont)%kami_action
    end.

  Definition multPull := MethodSig "multPull"(): Struct MultInStr.
  Definition multPush := MethodSig "multPush"(Struct MultOutStr): Void.

  Definition boothMultiplierImpl :=
    MODULE {
      Register "m_pos" : Bit MultBits <- Default
      with Register "m_neg" : Bit MultBits <- Default
      with Register "p" : Bit MultBits <- Default
      with Register "cnt" : Bit (S MultLogNumPhases) <- Default

      with Rule "boothMultRegister" :=
        Call src <- multPull();

        LET m : Bit (pred MultNumBitsExt + 1) <- #src!MultInStr@."multiplicand";
        LET m_neg <- (UniBit (Inv _) #m) + $1;

        LET m_pos : Bit MultBits <-
          BinBit (Concat _ (S MultNumBitsExt)) (UniBit (SignExtendTrunc _ _) #m) $0;
        LET m_neg : Bit MultBits <-
          BinBit (Concat _ (S MultNumBitsExt)) (UniBit (SignExtendTrunc _ _) #m_neg) $0;
        LET r <- #src!MultInStr@."multiplier";
        LET p : Bit MultBits <-
          BinBit (Concat (S MultNumBitsExt) _) $0 (BinBit (Concat _ 1) #r $0);

        (* Handle one bit in advance, in order to deal with other 64 bits 
         * consistently in a rule [boothStep].
         *)
        LET np : Bit MultBits <- boothStep m_pos m_neg #p;
        Write "m_pos" <- #m_pos;
        Write "m_neg" <- #m_neg;
        Write "p" <- #np;

        Write "cnt" : Bit (S MultLogNumPhases) <- $(MultNumPhases);
        Retv

      with Rule "boothMultGetResult" :=
        Read cnt : Bit MultLogNumPhases <- "cnt";
        Assert (#cnt == $0);

        Read p : Bit MultBits <- "p";
        LET highlowe : Bit (2 * MultNumBitsExt) <-
          UniBit (ConstExtract 1 (2 * MultNumBitsExt) 1) #p;
        LET highlow : Bit (2 * MultNumBits) <-
          UniBit (SignExtendTrunc _ _) #highlowe;
        
        LET high : Bit MultNumBits <- UniBit (TruncLsb _ _) #highlow;
        LET low : Bit MultNumBits <- UniBit (Trunc _ _) #highlow;

        LET res : Struct MultOutStr <- STRUCT { "high" ::= $$Default; "low" ::= #low };
        Call multPush(#res);

        Retv
            
      with Rule "boothStep" :=
        Read cnt : Bit MultLogNumPhases <- "cnt";
        Assert (#cnt != $0);

        Read m_pos : Bit MultBits <- "m_pos";
        Read m_neg : Bit MultBits <- "m_neg";
        Read p : Bit MultBits <- "p";

        Write "cnt" <- #cnt - $1;
        
        booth4Steps
          MultNumStepsPerPhase m_pos m_neg p
          (fun np => Write "p" <- #np; Retv)
    }.

  Definition multiplierSpec :=
    MODULE {
      Register "p" : Bit (2 * MultNumBitsExt) <- Default

      with Rule "multRegister" :=
        Call src <- multPull();
        LET m : Bit MultNumBitsExt <- #src!MultInStr@."multiplicand";
        LET m_ext : Bit (2 * MultNumBitsExt) <- UniBit (SignExtendTrunc _ _) #m;
        LET r : Bit MultNumBitsExt <- #src!MultInStr@."multiplier";
        LET r_ext : Bit (2 * MultNumBitsExt) <- UniBit (SignExtendTrunc _ _) #m;

        Write "p" <- #m_ext *s #r_ext;
        Retv

      with Rule "multGetResult" :=
        Read p : Bit (2 * MultNumBitsExt) <- "p";
        LET highlow : Bit (2 * MultNumBits) <- UniBit (SignExtendTrunc _ _) #p;
        
        LET high : Bit MultNumBits <- UniBit (TruncLsb _ _) #highlow;
        LET low : Bit MultNumBits <- UniBit (Trunc _ _) #highlow;

        LET res : Struct MultOutStr <- STRUCT { "high" ::= #high; "low" ::= #low };
        Call multPush(#res);

        Retv
    }.

  (*! Correctness of the multiplier *)

  Require Import ZArith.

  Section BoothEncoding.

    Inductive Booth := BZero | BPlus | BMinus.

    Definition boothToZ (b: Booth): Z :=
      match b with
      | BZero => 0
      | BPlus => 1
      | BMinus => -1
      end.

    Inductive bword: nat -> Set :=
    | BWO: bword 0
    | BWS: Booth -> forall n, bword n -> bword (S n).

    Fixpoint bwordToZ sz (bw: bword sz): Z :=
      match bw with
      | BWO => 0
      | BWS BZero bw' => bwordToZ bw' * 2
      | BWS BPlus bw' => (bwordToZ bw' * 2) + 1
      | BWS BMinus bw' => (bwordToZ bw' * 2) - 1
      end.

    Notation "w ~ 0" := (BWS BZero w) (at level 7, left associativity,
                                       format "w '~' '0'"): bword_scope.
    Notation "w ~ 'P'" := (BWS BPlus w) (at level 7, left associativity,
                                         format "w '~' 'P'"): bword_scope.
    Notation "w ~ 'N'" := (BWS BMinus w) (at level 7, left associativity,
                                          format "w '~' 'N'"): bword_scope.
    Delimit Scope bword_scope with bword.

    Definition wencodeB2 (w: word 2) :=
      if weq w WO~0~1 then BPlus
      else if weq w WO~1~0 then BMinus
           else BZero.

    Definition encodeB2 (mst lst: bool) :=
      match mst, lst with
      | false, true => BPlus
      | true, false => BMinus
      | _, _ => BZero
      end.

    Fixpoint wordToB2' sz (w: word sz) (p: bool): bword sz :=
      match w with
      | WO => BWO
      | WS b w' => BWS (encodeB2 b p) (wordToB2' w' b)
      end.

    Definition wordToB2 sz (w: word (S sz)): bword sz :=
      match w with
      | WO => idProp
      | WS b w' => wordToB2' w' b
      end.

    Lemma wordToB2_one:
      forall (w: word 1), bwordToZ (wordToB2 w) = 0%Z.
    Proof.
      intros.
    Admitted.

    Lemma wordToB2_bwordToZ:
      forall sz (w: word sz),
        bwordToZ (wordToB2 w~0) = wordToZ w.
    Proof.
    Admitted.

    Definition encodeB4 (b1 b2 b3: bool) :=
      match b1, b2, b3 with
      | false, false, true
      | false, true, false => (BZero, BPlus)
      | false, true, true => (BPlus, BZero)
      | true, false, false => (BMinus, BZero)
      | true, false, true
      | true, true, false => (BZero, BMinus)
      | _, _, _ => (BZero, BZero)
      end.

    (* Fixpoint wordToB4' sz (w: word sz) (p1 p2: bool): bword (S sz) := *)
    (*   match w with *)
    (*   | WO => BWO *)
    (*   | WS b WO => BWS (fst (encodeB4 p1 p2 b)) (BWS (snd (encodeB4 p1 p2 b)) BWO) *)
    (*   | WS b1 (WS b2 w') => *)
    (*     BWS (fst (encodeB4 p1 p2 b1)) (BWS (snd (encodeB4 p1 p2 b1)) (wordToB4' w' b1 b2)) *)
    (*   end. *)

  End BoothEncoding.

  Inductive BoothStepInv {sz} (m p: word sz)
    : forall wsz, word wsz (* the target word [w] *) ->
                  nat (* length of the lower part of [w] *) -> Prop :=
  | BSInv: forall sl su w wl wu u,
      wl = split1 (S sl) su w -> (* |wl| = S sl *)
      wu = split2 (S sl) su w -> (* |wu| = su *)
      wordToZ wu = (wordToZ m * u)%Z ->
      (u + bwordToZ (wordToB2 wl))%Z = wordToZ p ->
      BoothStepInv m p w (S sl).

  Lemma boothStepInv_intro:
    forall {sz} (m p: word sz) {wsz} (w: word wsz)
           sl su (wl: word (S sl)) (wu: word su) u
           (Hs: wsz = (S sl) + su),
      wl = split1 (S sl) su (eq_rect _ _ w _ Hs) ->
      wu = split2 (S sl) su (eq_rect _ _ w _ Hs) ->
      wordToZ wu = (wordToZ m * u)%Z ->
      (u + bwordToZ (wordToB2 wl))%Z = wordToZ p ->
      BoothStepInv m p w (S sl).
  Proof.
    intros; subst.
    econstructor; eauto.
  Qed.

  Lemma boothStepInv_inv:
    forall {sz} (m p: word sz) {wsz} (w: word wsz) swl,
      BoothStepInv m p w swl ->
      exists sl su (wl: word (S sl)) (wu: word su) u
             (Hs: wsz = (S sl) + su),
        swl = S sl /\
        wl = split1 (S sl) su (eq_rect _ _ w _ Hs) /\
        wu = split2 (S sl) su (eq_rect _ _ w _ Hs) /\
        wordToZ wu = (wordToZ m * u)%Z /\
        (u + bwordToZ (wordToB2 wl))%Z = wordToZ p.
  Proof.
    intros.
    inv H; destruct_existT.
    exists sl, su, (split1 (S sl) su w), (split2 (S sl) su w), u.
    exists eq_refl.
    repeat split; assumption.
  Qed.

  (*! TODO: move to word.v *)
  Lemma natToWord_wordToZ_0:
    forall sz, wordToZ (natToWord sz 0) = 0%Z.
  Proof.
  Admitted.

  Lemma boothStepInv_init:
    forall sz m p,
      BoothStepInv m (p: word sz)
                   (combine (combine (natToWord 1 0) p) (natToWord (S sz) 0))
                   (S sz).
  Proof.
    intros; econstructor; try reflexivity.
    - instantiate (1:= 0%Z).
      rewrite split2_combine.
      rewrite <-Zmult_0_r_reverse.
      apply natToWord_wordToZ_0.
    - rewrite Z.add_0_l.
      rewrite <-wordToB2_bwordToZ.
      do 2 f_equal.
      rewrite split1_combine.
      reflexivity.
  Qed.

  Lemma boothStepInv_finish:
    forall sz (m p: word sz) wsz (w: word (1 + wsz)),
      BoothStepInv m p w 1 ->
      wordToZ (split2 1 wsz w) = (wordToZ m * wordToZ p)%Z.
  Proof.
    intros.
    apply boothStepInv_inv in H; dest.
    inv H.

    rewrite wordToB2_one in H3.
    rewrite Z.add_0_r in H3; subst.
    rewrite <-H2; clear H2.

    assert (x0 = wsz) by (inv x4; reflexivity); subst.
    rewrite <-Eq_rect_eq.eq_rect_eq.
    reflexivity.
  Qed.

  Lemma boothStepInv_boothStep:
    forall (m: word MultNumBitsExt) mp mn p we nwe d,
      mp = combine (natToWord (S MultNumBitsExt) 0) (sext m _) ->
      mn = combine (natToWord (S MultNumBitsExt) 0) (sext (wneg m) _) ->
      boothStep mp mn we = nwe ->
      BoothStepInv m p (evalExpr we) d ->
      (d > 1)%nat ->
      BoothStepInv m p (evalExpr nwe) (d - 1).
  Proof.
    intros; subst.
    apply boothStepInv_inv in H2.
    destruct H2 as [sl [su [wl [wu [u [Hs ?]]]]]]; dest.
    subst d.
    
    remember (eq_rect _ word (evalExpr we) _ Hs) as ws.

    destruct sl as [|sl]; [omega|].
    change (S (S sl) - 1) with (S sl).

    assert (Hsn: MultBits = S sl + S su).
    { replace MultBits with (MultBits - 2 + 2) by reflexivity.
      omega.
    }

    (* set (split1 2 _ wl) as wlLsb2. *)
    (* set (boothToZ (wencodeB2 wlLsb2)) as b. *)

    rewrite boothStep_eval.
    remember (evalExpr we) as w; clear Heqw we.

    destruct (weq _ _).
    
    - eapply boothStepInv_intro; try reflexivity.

    
  Admitted.
  
  (* ["m_pos"; "m_neg"; "p"; "cnt"] ~ ["p"] *)
  Local Definition thetaR (ir sr: RegsT): Prop.
  Proof.
    kexistv "m_pos" m_pos ir (Bit MultBits).
    kexistv "m_neg" m_neg ir (Bit MultBits).
    exact False. (* TODO *)
  Defined.

  Theorem multiplier_ok: boothMultiplierImpl <<== multiplierSpec.
  Proof.
    (* kdecomposeR_nodefs thetaR. *)

  Admitted.

End Multiplier64.


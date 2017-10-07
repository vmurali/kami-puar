Require Import Kami.
Require Import Lib.NatLib Lib.Indexer Lib.Struct Lib.FMap Lib.Reflection.
Require Import Kami.Tactics Kami.SemFacts Kami.StepDet.
Require Import Puar.WordFacts Puar.Useful FunctionalExtensionality.

Require Import Eqdep Program.Equality.

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
      wrshifta (if weq (split1 2 (MultBits - 2) (evalExpr p)) WO~0~1
                then evalExpr p ^+ m_pos
                else if weq (split1 2 (MultBits - 2) (evalExpr p)) WO~1~0
                     then evalExpr p ^+ m_neg
                     else evalExpr p) 1.
  Proof.
    intros; unfold boothStep.
    unfold evalExpr; fold evalExpr.
    unfold evalBinBit.
    rewrite boothStep'_eval.

    destruct (weq _ _); [reflexivity|].
    destruct (weq _ _); reflexivity.
  Qed.

  Opaque boothStep.

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
    ((booth4Step' m_pos m_neg p (UniBit (Trunc 3 _) p)) ~>> $$(WO~1~0))%kami_expr.

  Lemma booth4Step'_eval:
    forall m_pos m_neg p pr,
      evalExpr (booth4Step' m_pos m_neg p pr) =
      if weq (evalExpr pr) WO~0~0~1 then evalExpr p ^+ m_pos
      else if weq (evalExpr pr) WO~0~1~0 then evalExpr p ^+ m_pos
      else if weq (evalExpr pr) WO~0~1~1 then evalExpr p ^+ (wlshift m_pos 1)
      else if weq (evalExpr pr) WO~1~0~0 then evalExpr p ^+ (wlshift m_neg 1)
      else if weq (evalExpr pr) WO~1~0~1 then evalExpr p ^+ m_neg
      else if weq (evalExpr pr) WO~1~1~0 then evalExpr p ^+ m_neg
      else evalExpr p.
  Proof.
    intros; simpl.
    repeat destruct (weq _ _); reflexivity.
  Qed.

  Definition booth4StepEvalM (m_pos m_neg: word MultBits)
             (p: Expr type (SyntaxKind (Bit (MultBits - 3 + 3)))) :=
    if weq (split1 3 (MultBits - 3) (evalExpr p)) WO~0~0~1
    then m_pos
    else
      if weq (split1 3 (MultBits - 3) (evalExpr p)) WO~0~1~0
      then m_pos
      else
        if weq (split1 3 (MultBits - 3) (evalExpr p)) WO~0~1~1
        then (wlshift m_pos 1)
        else
          if weq (split1 3 (MultBits - 3) (evalExpr p)) WO~1~0~0
          then (wlshift m_neg 1)
          else
            if weq (split1 3 (MultBits - 3) (evalExpr p)) WO~1~0~1
            then m_neg
            else
              if weq (split1 3 (MultBits - 3) (evalExpr p)) WO~1~1~0
              then m_neg
              else $0.

  Lemma booth4Step_eval:
    forall m_pos m_neg p,
      evalExpr (booth4Step m_pos m_neg p) =
      wrshifta
        ((evalExpr p)
           ^+ (booth4StepEvalM m_pos m_neg p)) 2.
  Proof.
    intros; unfold booth4Step, booth4StepEvalM.
    unfold evalExpr; fold evalExpr.
    unfold evalBinBit.
    rewrite booth4Step'_eval.

    repeat destruct (weq _ _); try reflexivity.
    rewrite wplus_comm, wplus_unit; reflexivity.
  Qed.

  Opaque booth4Step.
  
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
      with Register "m" : Bit MultNumBitsExt <- Default
      with Register "r" : Bit MultNumBitsExt <- Default
      with Register "cnt" : Bit (S MultLogNumPhases) <- Default

      with Rule "boothMultRegister" :=
        Call src <- multPull();

        LET m : Bit (pred MultNumBitsExt + 1) <- #src!MultInStr@."multiplicand";
        LET m_neg <- UniBit (Inv _) #m;

        LET m_pos : Bit MultBits <-
          BinBit (Concat _ (S MultNumBitsExt))
                 (UniBit (SignExtendTrunc _ (S MultNumBitsExt)) #m) $0;
        LET m_neg : Bit MultBits <-
          BinBit (Concat _ (S MultNumBitsExt))
                 (UniBit (SignExtendTrunc _ (S MultNumBitsExt)) #m_neg) $0;

        Write "m_pos" <- #m_pos;
        Write "m_neg" <- #m_neg;
        Write "m" <- #m;

        LET r <- #src!MultInStr@."multiplier";
        Write "r" <- #r;

        LET p : Bit MultBits <-
          BinBit (Concat (S MultNumBitsExt) _) $0 (BinBit (Concat _ 1) #r $0);
        LET m_pos_ex <- #m_pos << $$(WO~1);
        LET m_neg_ex <- #m_neg << $$(WO~1);
        
        (* Handle one bit in advance, in order to deal with other 64 bits 
         * consistently in a rule [boothStep].
         *)
        LET np : Bit MultBits <- boothStep m_pos_ex m_neg_ex #p;
        Write "p" <- #np;

        Write "cnt" : Bit (S MultLogNumPhases) <- $(MultNumPhases);
        Retv

      with Rule "boothMultGetResult" :=
        Read cnt : Bit (S MultLogNumPhases) <- "cnt";
        Assert (#cnt == $0);

        Read p : Bit MultBits <- "p";
        LET highlowe : Bit (2 * MultNumBitsExt) <-
          UniBit (ConstExtract 1 (2 * MultNumBitsExt) 1) #p;
        LET highlow : Bit (2 * MultNumBits) <-
          UniBit (SignExtendTrunc _ _) #highlowe;
        
        LET high : Bit MultNumBits <- UniBit (TruncLsb _ _) #highlow;
        LET low : Bit MultNumBits <- UniBit (Trunc _ _) #highlow;

        Call multPush(STRUCT { "high" ::= #high; "low" ::= #low });

        Retv
            
      with Rule "boothStep" :=
        Read cnt : Bit (S MultLogNumPhases) <- "cnt";
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
      Register "m" : Bit MultNumBitsExt <- Default
      with Register "r" : Bit MultNumBitsExt <- Default

      with Rule "multRegister" :=
        Call src <- multPull();
        LET m : Bit MultNumBitsExt <- #src!MultInStr@."multiplicand";
        LET r : Bit MultNumBitsExt <- #src!MultInStr@."multiplier";

        Write "m" <- #m;
        Write "r" <- #r;
        Retv

      with Rule "multGetResult" :=
        Read m : Bit MultNumBitsExt <- "m";
        LET m_ext : Bit (2 * MultNumBitsExt) <- UniBit (SignExtendTrunc _ _) #m;
        Read r : Bit MultNumBitsExt <- "r";
        LET r_ext : Bit (2 * MultNumBitsExt) <- UniBit (SignExtendTrunc _ _) #r;

        LET p : Bit (2 * MultNumBitsExt) <- #m_ext *s #r_ext;
        LET highlow : Bit (2 * MultNumBits) <- UniBit (SignExtendTrunc _ _) #p;
        
        LET high : Bit MultNumBits <- UniBit (TruncLsb _ _) #highlow;
        LET low : Bit MultNumBits <- UniBit (Trunc _ _) #highlow;

        Call multPush(STRUCT { "high" ::= #high; "low" ::= #low });

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

    Definition bbToZ (bb: Booth * Booth): Z :=
      match bb with
      | (BZero, b) => boothToZ b
      | (BPlus, b) => boothToZ b + 2
      | (BMinus, b) => boothToZ b - 2
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

    Definition encodeB2 (mst lst: bool) :=
      match mst, lst with
      | false, true => BPlus
      | true, false => BMinus
      | _, _ => BZero
      end.

    Definition wencodeB2 (w: word 2): Booth.
    Proof.
      dependent destruction w.
      dependent destruction w.
      exact (encodeB2 b0 b).
    Defined.

    Fixpoint wordToB2' sz (w: word sz) (p: bool): bword sz :=
      match w with
      | WO => BWO
      | WS b w' => BWS (encodeB2 b p) (wordToB2' w' b)
      end.

    Lemma wordToB2'_rtrunc1_wlsb:
      forall sz (w: word (S sz)) p,
        wordToB2' w p = BWS (encodeB2 (wlsb w) p) (wordToB2' (rtrunc1 w) (wlsb w)).
    Proof.
      intros; dependent destruction w; simpl; reflexivity.
    Qed.

    Definition wordToB2 sz (w: word (S sz)): bword sz :=
      match w with
      | WO => idProp
      | WS b w' => wordToB2' w' b
      end.

    Lemma wordToB2_one:
      forall (w: word 1), bwordToZ (wordToB2 w) = 0%Z.
    Proof.
      dependent destruction w.
      dependent destruction w.
      simpl; reflexivity.
    Qed.

    Lemma wordToB2_bwordToZ:
      forall sz (w: word sz),
        bwordToZ (wordToB2 w~0) = wordToZ w.
    Proof.
    Admitted.

    Lemma wordToB2_bwordToZ_step:
      forall sz (w: word (S (S sz))),
        bwordToZ (wordToB2 w) =
        (2 * (bwordToZ (wordToB2 (rtrunc1 w)) +
              boothToZ (wencodeB2 (split1 2 _ w))))%Z.
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

    Definition wencodeB4 (w: word 3): Booth * Booth.
    Proof.
      dependent destruction w.
      dependent destruction w.
      dependent destruction w.
      exact (encodeB4 b1 b0 b).
    Defined.

    Fixpoint wordToB4' sz (w: word sz) (p1 p2: bool): bword (S sz).
    Proof.
      dependent destruction w.
      - exact (BWS (encodeB2 p1 p2) BWO).
      - dependent destruction w.
        + exact (BWS (snd (encodeB4 b p1 p2)) (BWS (fst (encodeB4 b p1 p2)) BWO)).
        + refine (BWS (snd (encodeB4 b p1 p2)) (BWS (fst (encodeB4 b p1 p2)) _)).
          exact (wordToB4' _ w b0 b).
    Defined.

    Definition wordToB4 sz (w: word (S sz)): bword sz.
    Proof.
      dependent destruction w.
      dependent destruction w.
      - exact BWO.
      - exact (wordToB4' w b0 b).
    Defined.

    Lemma wordToB2_wordToB4:
      forall sz (w: word (S sz)),
        bwordToZ (wordToB2 w) = bwordToZ (wordToB4 w).
    Proof.
    Admitted.

    Lemma wordToB4_bwordToZ_step:
      forall sz (w: word (S (S (S sz)))),
        bwordToZ (wordToB4 w) =
        (4 * bwordToZ (wordToB4 (rtrunc2 w)) +
         bbToZ (wencodeB4 (split1 3 _ w)))%Z.
    Proof.
    Admitted.

  End BoothEncoding.

  Inductive BoothStepInv {sz} (m p: word sz)
    : forall sl, word sl -> forall su, word su -> Prop :=
  | BSInv: forall sl su (wl: word (S sl)) (wu: word su) u tsu (twu: word tsu),
      existT word _ wu = existT word _ (sext twu 1) ->
      wordToZ wu = (wordToZ m * u)%Z ->
      (u + bwordToZ (wordToB2 wl) * Z.of_nat (pow2 (su - sz - 1)))%Z = wordToZ p ->
      BoothStepInv m p wl wu.

  Lemma boothStepInv_inv:
    forall {sz} (m p: word sz) sl su (wl: word (S sl)) (wu: word su),
      BoothStepInv m p wl wu ->
      exists u tsu (twu: word tsu),
        existT word _ wu = existT word _ (sext twu 1) /\
        wordToZ wu = (wordToZ m * u)%Z /\
        (u + bwordToZ (wordToB2 wl) * Z.of_nat (pow2 (su - sz - 1)))%Z = wordToZ p.
  Proof.
    intros.
    inv H; destruct_existT.
    repeat eexists; try eassumption.
  Qed.

  Lemma natToWord_ZToWord_zero:
    forall sz, natToWord sz 0 = ZToWord sz 0%Z.
  Proof.
    intros; simpl.
    induction sz; simpl; auto.
    rewrite IHsz; reflexivity.
  Qed.

  Lemma wmsb_wzero'_false:
    forall sz, wmsb (wzero' sz) false = false.
  Proof.
    induction sz; simpl; intros; auto.
  Qed.

  Lemma boothStepInv_init:
    forall sz m p,
      BoothStepInv m (p: word sz)
                   (combine (natToWord 1 0) p)
                   (natToWord (S sz) 0).
  Proof.
    intros; econstructor; try reflexivity.
    - instantiate (1:= (natToWord sz 0)).
      replace (S sz) with (sz + 1) by omega.
      rewrite sext_zero; reflexivity.
    - instantiate (1:= 0%Z).
      rewrite <-Zmult_0_r_reverse.
      rewrite natToWord_ZToWord_zero.
      rewrite wordToZ_wzero'.
      reflexivity.
    - rewrite Z.add_0_l.
      replace (S sz - sz - 1) with 0 by omega.
      simpl; rewrite <-wordToB2_bwordToZ.
      rewrite Z.mul_1_r.
      reflexivity.
  Qed.

  Lemma boothStepInv_finish:
    forall {sz} (m p: word sz) (wl: word 1) su (wu: word su),
      BoothStepInv m p wl wu ->
      exists tsu (twu: word tsu),
        existT word _ wu = existT word _ (sext twu 1) /\
        wordToZ wu = (wordToZ m * wordToZ p)%Z.
  Proof.
    intros.
    apply boothStepInv_inv in H; dest.
    rewrite wordToB2_one in H1.
    rewrite Z.add_0_r in H1; subst.
    repeat eexists; eassumption.
  Qed.

  Definition booth4AddM (m: word MultNumBitsExt) (wl: word 3) {sus}
    : word (S sus + MultNumBitsExt + 2).
  Proof.
    assert (Hsu: sus + (MultNumBitsExt + 1 + 2) = S sus + MultNumBitsExt + 2)
      by (abstract omega).
    refine (if weq wl WO~0~0~1 then _
            else if weq wl WO~0~1~0 then _
                 else if weq wl WO~0~1~1 then _
                      else if weq wl WO~1~0~0 then _
                           else if weq wl WO~1~0~1 then _
                                else if weq wl WO~1~1~0 then _
                                     else _).
    - exact (eq_rect _ word (extz (sext (sext m 1) 2) sus) _ Hsu).
    - exact (eq_rect _ word (extz (sext (sext m 1) 2) sus) _ Hsu).
    - exact (sext (extz m (S sus)) 2).
    - exact (sext (extz (wneg m) (S sus)) 2).
    - exact (eq_rect _ word (extz (sext (sext (wneg m) 1) 2) sus) _ Hsu).
    - exact (eq_rect _ word (extz (sext (sext (wneg m) 1) 2) sus) _ Hsu).
    - exact $0.
  Defined.

  Lemma booth4AddM_sext:
    forall m wl sus,
    exists w, booth4AddM (sus:= sus) m wl = sext w 2.
  Proof.
    unfold booth4AddM; intros.
    repeat destruct (weq _ _).
    - pose proof (extz_sext_eq_rect (sext m 1) 2 sus (booth4AddM_subproof sus)); dest.
      rewrite H.
      pose proof (sext_eq_rect (extz (sext m 1) sus) 2 (S sus + MultNumBitsExt) x); dest.
      rewrite H0.
      eexists; reflexivity.
    - pose proof (extz_sext_eq_rect (sext m 1) 2 sus (booth4AddM_subproof sus)); dest.
      rewrite H.
      pose proof (sext_eq_rect (extz (sext m 1) sus) 2 (S sus + MultNumBitsExt) x); dest.
      rewrite H0.
      eexists; reflexivity.
    - eexists; reflexivity.
    - eexists; reflexivity.
    - pose proof (extz_sext_eq_rect (sext (wneg m) 1) 2 sus (booth4AddM_subproof sus)); dest.
      rewrite H.
      pose proof (sext_eq_rect (extz (sext (wneg m) 1) sus) 2 (S sus + MultNumBitsExt) x); dest.
      rewrite H0.
      eexists; reflexivity.
    - pose proof (extz_sext_eq_rect (sext (wneg m) 1) 2 sus (booth4AddM_subproof sus)); dest.
      rewrite H.
      pose proof (sext_eq_rect (extz (sext (wneg m) 1) sus) 2 (S sus + MultNumBitsExt) x); dest.
      rewrite H0.
      eexists; reflexivity.
    - exists (natToWord _ 0).
      apply eq_sym, sext_zero.
  Qed.

  Definition booth4AddU (wl: word 3) (sus: nat) :=
    (if weq wl WO~0~0~1 then (Z.of_nat (pow2 sus))
     else if weq wl WO~0~1~0 then (Z.of_nat (pow2 sus))
          else if weq wl WO~0~1~1 then (Z.of_nat (pow2 (S sus)))
               else if weq wl WO~1~0~0 then -(Z.of_nat (pow2 (S sus)))
                    else if weq wl WO~1~0~1 then -(Z.of_nat (pow2 sus))
                         else if weq wl WO~1~1~0 then -(Z.of_nat (pow2 sus))
                              else 0)%Z.

  Lemma wencodeB4_zero:
    forall (wl: word 3),
      wl <> WO~0~0~1 -> wl <> WO~0~1~0 -> wl <> WO~0~1~1 ->
      wl <> WO~1~0~0 -> wl <> WO~1~0~1 -> wl <> WO~1~1~0 ->
      wencodeB4 wl = (BZero, BZero).
  Proof.
    intros.
    dependent destruction wl.
    dependent destruction wl.
    dependent destruction wl.
    dependent destruction wl.
    destruct b, b0, b1; intuition idtac.
  Qed.

  Lemma booth4StepEvalM_booth4AddM:
    forall (m: word MultNumBitsExt) we sl sus,
      MultBits - 3 + 3 = S (S (S sl)) + (S sus + MultNumBitsExt) ->
      existT word (2 + (MultNumBitsExt - 1) + S MultNumBitsExt)
             (wrshifta
                (booth4StepEvalM (extz (sext m 1) (2 + (MultNumBitsExt - 1)))
                                 (extz (sext (^~ m) 1) (2 + (MultNumBitsExt - 1))) we) 2) =
      existT word (S sl + (S sus + MultNumBitsExt + 2))
             (extz (booth4AddM m (split1 3 (MultBits - 3) (evalExpr we))) (S sl)).
  Proof.
    unfold booth4StepEvalM, booth4AddM; intros.
    repeat destruct (weq _ _).

    - rewrite wrshifta_extz_sext.
      rewrite <-extz_sext.
      replace (MultNumBitsExt - 1) with (S sl + (MultNumBitsExt - 1 - (S sl)))
        by (assert (MultNumBitsExt - 1 >= S sl)%nat
             by (cbn; cbn in H; omega); omega).
      rewrite <-extz_extz.
      apply existT_extz.
      rewrite existT_eq_rect.
      replace (MultNumBitsExt - 1 - S sl) with sus; [reflexivity|].
      assert (S (S (S sl)) + sus = MultBits - MultNumBitsExt - 1) by omega.
      simpl in H0; assert (S (sl + sus) = 64) by omega.
      apply eq_sym, Nat.add_sub_eq_l.
      simpl; rewrite H1; reflexivity.
    - rewrite wrshifta_extz_sext.
      rewrite <-extz_sext.
      replace (MultNumBitsExt - 1) with (S sl + (MultNumBitsExt - 1 - (S sl)))
        by (assert (MultNumBitsExt - 1 >= S sl)%nat
             by (cbn; cbn in H; omega); omega).
      rewrite <-extz_extz.
      apply existT_extz.
      rewrite existT_eq_rect.
      replace (MultNumBitsExt - 1 - S sl) with sus; [reflexivity|].
      assert (S (S (S sl)) + sus = MultBits - MultNumBitsExt - 1) by omega.
      simpl in H0; assert (S (sl + sus) = 64) by omega.
      apply eq_sym, Nat.add_sub_eq_l.
      simpl; rewrite H1; reflexivity.

    - rewrite extz_sext.
      rewrite existT_sext with (w2:= extz m (S sl + S sus)) by apply extz_extz.
      rewrite <-wrshifta_extz_sext.
      apply existT_wrshifta.
      rewrite existT_wlshift
        with (w2:= sext (extz m (2 + (MultNumBitsExt - 1))) 1)
        by (rewrite <-extz_sext; reflexivity).
      rewrite wlshift_sext_extz.
      rewrite extz_extz.
      replace (S sl + S sus) with MultNumBitsExt by (cbn; cbn in H; omega).
      reflexivity.
    - rewrite extz_sext.
      rewrite existT_sext with (w2:= extz (wneg m) (S sl + S sus))
        by apply extz_extz.
      rewrite <-wrshifta_extz_sext.
      apply existT_wrshifta.
      rewrite existT_wlshift
        with (w2:= sext (extz (wneg m) (2 + (MultNumBitsExt - 1))) 1)
        by (rewrite <-extz_sext; reflexivity).
      rewrite wlshift_sext_extz.
      rewrite extz_extz.
      replace (S sl + S sus) with MultNumBitsExt by (cbn; cbn in H; omega).
      reflexivity.

    - rewrite wrshifta_extz_sext.
      rewrite <-extz_sext.
      replace (MultNumBitsExt - 1) with (S sl + (MultNumBitsExt - 1 - (S sl)))
        by (assert (MultNumBitsExt - 1 >= S sl)%nat
             by (cbn; cbn in H; omega); omega).
      rewrite <-extz_extz.
      apply existT_extz.
      rewrite existT_eq_rect.
      replace (MultNumBitsExt - 1 - S sl) with sus; [reflexivity|].
      assert (S (S (S sl)) + sus = MultBits - MultNumBitsExt - 1) by omega.
      simpl in H0; assert (S (sl + sus) = 64) by omega.
      apply eq_sym, Nat.add_sub_eq_l.
      simpl; rewrite H1; reflexivity.
    - rewrite wrshifta_extz_sext.
      rewrite <-extz_sext.
      replace (MultNumBitsExt - 1) with (S sl + (MultNumBitsExt - 1 - (S sl)))
        by (assert (MultNumBitsExt - 1 >= S sl)%nat
             by (cbn; cbn in H; omega); omega).
      rewrite <-extz_extz.
      apply existT_extz.
      rewrite existT_eq_rect.
      replace (MultNumBitsExt - 1 - S sl) with sus; [reflexivity|].
      assert (S (S (S sl)) + sus = MultBits - MultNumBitsExt - 1) by omega.
      simpl in H0; assert (S (sl + sus) = 64) by omega.
      apply eq_sym, Nat.add_sub_eq_l.
      simpl; rewrite H1; reflexivity.

    - rewrite wrshifta_zero.
      rewrite extz_zero.
      replace (S sl + (S sus + MultNumBitsExt + 2)) with MultBits by omega.
      reflexivity.
  Qed.
  
  Lemma booth4AddM_booth4AddU:
    forall sus m wu w,
      wordToZ (sext wu 2 ^+ booth4AddM (sus:= sus) m (split1 3 (MultBits - 3) w)) =
      (wordToZ wu + wordToZ m * booth4AddU (split1 3 (MultBits - 3) w) sus)%Z.
  Proof.
    unfold booth4AddM, booth4AddU; intros.
    repeat destruct (weq _ _).

    - pose proof (extz_sext_eq_rect (sext m 1) 2 sus (booth4AddM_subproof sus)).
      destruct H as [Hsu' ?].
      rewrite H.
      pose proof (sext_eq_rect (extz (sext m 1) sus) 2 _ Hsu').
      destruct H0 as [Hsu'' ?].
      rewrite H0.
      rewrite sext_wplus_wordToZ_distr by discriminate.
      do 2 rewrite sext_wordToZ.
      rewrite wordToZ_eq_rect.
      rewrite extz_pow2_wordToZ.
      rewrite sext_wordToZ.
      reflexivity.
    - pose proof (extz_sext_eq_rect (sext m 1) 2 sus (booth4AddM_subproof sus)).
      destruct H as [Hsu' ?].
      rewrite H.
      pose proof (sext_eq_rect (extz (sext m 1) sus) 2 _ Hsu').
      destruct H0 as [Hsu'' ?].
      rewrite H0.
      rewrite sext_wplus_wordToZ_distr by discriminate.
      do 2 rewrite sext_wordToZ.
      rewrite wordToZ_eq_rect.
      rewrite extz_pow2_wordToZ.
      rewrite sext_wordToZ.
      reflexivity.

    - rewrite sext_wplus_wordToZ_distr by discriminate.
      do 2 rewrite sext_wordToZ.
      rewrite extz_pow2_wordToZ.
      reflexivity.
    - rewrite sext_wplus_wordToZ_distr by discriminate.
      do 2 rewrite sext_wordToZ.
      rewrite extz_pow2_wordToZ.
      rewrite wneg_wordToZ.
      ring.

    - pose proof (extz_sext_eq_rect (sext (wneg m) 1) 2 sus (booth4AddM_subproof sus)).
      destruct H as [Hsu' ?].
      rewrite H.
      pose proof (sext_eq_rect (extz (sext (wneg m) 1) sus) 2 _ Hsu').
      destruct H0 as [Hsu'' ?].
      rewrite H0.
      rewrite sext_wplus_wordToZ_distr by discriminate.
      do 2 rewrite sext_wordToZ.
      rewrite wordToZ_eq_rect.
      rewrite extz_pow2_wordToZ.
      rewrite sext_wordToZ.
      rewrite wneg_wordToZ.
      ring.
    - pose proof (extz_sext_eq_rect (sext (wneg m) 1) 2 sus (booth4AddM_subproof sus)).
      destruct H as [Hsu' ?].
      rewrite H.
      pose proof (sext_eq_rect (extz (sext (wneg m) 1) sus) 2 _ Hsu').
      destruct H0 as [Hsu'' ?].
      rewrite H0.
      rewrite sext_wplus_wordToZ_distr by discriminate.
      do 2 rewrite sext_wordToZ.
      rewrite wordToZ_eq_rect.
      rewrite extz_pow2_wordToZ.
      rewrite sext_wordToZ.
      rewrite wneg_wordToZ.
      ring.

    - rewrite wplus_comm, wplus_unit.
      rewrite sext_wordToZ.
      rewrite Z.mul_0_r.
      ring.
  Qed.

  Lemma booth4AddU_bbToZ:
    forall wl n,
      booth4AddU wl n =
      (bbToZ (wencodeB4 wl) * Z.of_nat (pow2 n))%Z.
  Proof.
    unfold booth4AddU, bbToZ; intros.
    repeat destruct (weq _ _); subst.
    - simpl; destruct (Z.of_nat (pow2 n)); reflexivity.
    - simpl; destruct (Z.of_nat (pow2 n)); reflexivity.
    - rewrite pow2_S_z; simpl; reflexivity.
    - rewrite pow2_S_z; simpl.
      destruct (Z.of_nat (pow2 n)); reflexivity.
    - simpl; destruct (Z.of_nat (pow2 n)); reflexivity.
    - simpl; destruct (Z.of_nat (pow2 n)); reflexivity.
    - rewrite wencodeB4_zero by assumption.
      reflexivity.
  Qed.

  Lemma boothStepInv_booth4Step:
    forall (m: word MultNumBitsExt) mp mn p we nwe,
      mp = extz (sext m 1) (S MultNumBitsExt) ->
      mn = extz (sext (wneg m) 1) (S MultNumBitsExt) ->
      booth4Step mp mn we = nwe ->
      forall sl su (wl: word (S (S (S sl)))) (wu: word su) sus,
        (S sus) + MultNumBitsExt = su ->
        existT word _ (evalExpr we) = existT word _ (combine wl wu) ->
        BoothStepInv m p wl wu ->
        exists (nwl: word (S sl)) (nwu: word (su + 2)),
          existT word _ (evalExpr nwe) = existT word _ (combine nwl nwu) /\
          BoothStepInv m p nwl nwu.
  Proof.
    intros; subst.
    apply boothStepInv_inv in H4.
    rewrite wordToB2_wordToB4 in H4.
    destruct H4 as [u ?]; dest.

    exists (rtrunc2 wl).
    exists (sext wu 2 ^+ (booth4AddM m (split1 3 (MultBits - 3) (evalExpr we)))).
    split.

    - rewrite booth4Step_eval.
      rewrite wrshifta_wplus.
      rewrite combine_wplus.
      apply existT_wplus.
      * apply combine_wrshifta_rtrunc2_sext; auto.
      * apply eq_sigT_fst in H3.
        change (S MultNumBitsExt) with (2 + (MultNumBitsExt - 1)).
        change (MultBits - 3 + 3) with (2 + (MultNumBitsExt - 1) + (S MultNumBitsExt)).
        auto using booth4StepEvalM_booth4AddM.

    - pose proof (booth4AddM_sext m (split1 3 (MultBits - 3) (evalExpr we)) sus); dest.
      eapply BSInv
        with (u0:= (u + booth4AddU (split1 3 (MultBits - 3) (evalExpr we)) sus)%Z).
      + rewrite H2.
        rewrite sext_wplus.
        replace 2 with (1 + 1) by reflexivity.
        rewrite sext_sext.
        reflexivity.
      + rewrite Z.mul_add_distr_l, <-H0.
        apply booth4AddM_booth4AddU.
      + rewrite wordToB2_wordToB4.
        rewrite <-H1, <-Z.add_assoc.
        replace (S sus + MultNumBitsExt + 2 - MultNumBitsExt - 1)
          with (S (S sus)) by omega.
        apply Z.add_cancel_l.
        replace (S sus + MultNumBitsExt - MultNumBitsExt - 1) with sus by omega.
        rewrite wordToB4_bwordToZ_step.
        rewrite Z.mul_add_distr_r.
        rewrite Z.add_comm.
        f_equal.
        * replace (Z.of_nat (pow2 (S (S sus)))) with (4 * Z.of_nat (pow2 sus))%Z
            by (do 2 rewrite pow2_S_z; ring).
          rewrite Z.mul_assoc; f_equal; omega.
        * replace (split1 3 (MultBits - 3) (evalExpr we)) with (split1 3 sl wl)
            by (apply eq_sym; eauto using split1_combine_existT).
          apply booth4AddU_bbToZ.
  Qed.

  Lemma boothStepInv_boothStep:
    forall (m: word MultNumBitsExt) mp mn p we nwe,
      mp = extz m (S (S MultNumBitsExt)) ->
      mn = extz (wneg m) (S (S MultNumBitsExt)) ->
      boothStep mp mn we = nwe ->
      forall sl su (wl: word (S (S sl))) (wu: word su) sus,
        (S sus) + MultNumBitsExt = su ->
        existT word _ (evalExpr we) = existT word _ (combine wl wu) ->
        BoothStepInv m p wl wu ->
        exists (nwl: word (S sl)) (nwu: word (su + 1)),
          existT word _ (evalExpr nwe) = existT word _ (combine nwl nwu) /\
          BoothStepInv m p nwl nwu.
  Proof.
    intros; subst.
    apply boothStepInv_inv in H4.
    destruct H4 as [u ?]; dest.
    rewrite boothStep_eval.
    remember (evalExpr we) as w; clear Heqw we.
    destruct (weq _ _); [|destruct (weq _ _)].

    - exists (rtrunc1 wl).
      exists (sext wu 1 ^+ sext (extz m (S sus)) 1).
      split.
      + rewrite wrshifta_wplus.
        rewrite combine_wplus.
        apply existT_wplus.
        * apply combine_wrshifta_rtrunc1_sext; auto.
        * change (S (S MultNumBitsExt)) with (1 + (S MultNumBitsExt)).
          change (MultBits - 2 + 2) with (1 + (S MultNumBitsExt) + MultNumBitsExt).
          rewrite wrshifta_extz_sext.
          rewrite extz_sext.
          apply existT_sext.
          rewrite extz_extz.
          replace (S sl + S sus) with (S MultNumBitsExt); [reflexivity|].
          clear -H3; apply eq_sigT_fst in H3.
          cbn; cbn in H3; omega.
      + eapply BSInv with (u0:= (u + Z.of_nat (pow2 (S sus)))%Z).
        * rewrite sext_wplus.
          reflexivity.
        * rewrite Z.mul_add_distr_l, <-H0.
          rewrite sext_wplus_wordToZ_distr by discriminate.
          f_equal.
          { apply sext_wordToZ. }
          { rewrite sext_wordToZ.
            apply extz_pow2_wordToZ.
          }
        * rewrite <-H1, <-Z.add_assoc.
          replace (S sus + MultNumBitsExt + 1 - MultNumBitsExt - 1) with (S sus) by omega.
          replace (S sus + MultNumBitsExt - MultNumBitsExt - 1) with sus by omega.
          replace (Z.of_nat (pow2 (S sus))) with (1 * Z.of_nat (pow2 (S sus)))%Z at 1 by ring.
          rewrite <-Z.mul_add_distr_r.
          replace (Z.of_nat (pow2 (S sus))) with (Z.of_nat 2 * Z.of_nat (pow2 sus))%Z
            by (apply eq_sym, Nat2Z.inj_mul).
          rewrite Z.mul_assoc.
          rewrite wordToB2_bwordToZ_step.
          replace (split1 2 sl wl) with (WO~0~1)
            by (erewrite <-split1_combine_existT; eauto).
          change (boothToZ (wencodeB2 WO~0~1)) with 1%Z.
          ring.
      
    - exists (rtrunc1 wl).
      exists (sext wu 1 ^+ sext (extz (^~ m) (S sus)) 1).
      split.
      + rewrite wrshifta_wplus.
        rewrite combine_wplus.
        apply existT_wplus.
        * apply combine_wrshifta_rtrunc1_sext; auto.
        * change (S (S MultNumBitsExt)) with (1 + (S MultNumBitsExt)).
          change (MultBits - 2 + 2) with (1 + (S MultNumBitsExt) + MultNumBitsExt).
          rewrite wrshifta_extz_sext.
          rewrite extz_sext.
          apply existT_sext.
          rewrite extz_extz.
          replace (S sl + S sus) with (S MultNumBitsExt); [reflexivity|].
          (* NOTE: [omega] can't solve this :( *)
          clear -H3; apply eq_sigT_fst in H3.
          cbn; cbn in H3; omega.
      + eapply BSInv with (u0:= (u - Z.of_nat (pow2 (S sus)))%Z).
        * rewrite sext_wplus.
          reflexivity.
        * rewrite Z.mul_sub_distr_l, <-H0.
          rewrite sext_wplus_wordToZ_distr by discriminate.
          do 2 rewrite sext_wordToZ.
          rewrite extz_wneg.
          rewrite wneg_wordToZ'.
          f_equal.
          apply extz_pow2_wordToZ.
        * rewrite <-H1.
          rewrite Z.add_comm with (n:= (u - _)%Z).
          rewrite Z.add_sub_assoc.
          rewrite Z.add_sub_swap.
          rewrite Z.add_comm with (n:= u).
          replace (S sus + MultNumBitsExt + 1 - MultNumBitsExt - 1) with (S sus) by omega.
          replace (S sus + MultNumBitsExt - MultNumBitsExt - 1) with sus by omega.
          replace (Z.of_nat (pow2 (S sus))) with (1 * Z.of_nat (pow2 (S sus)))%Z at 2 by ring.
          rewrite <-Z.mul_sub_distr_r.
          replace (Z.of_nat (pow2 (S sus))) with (Z.of_nat 2 * Z.of_nat (pow2 sus))%Z
            by (apply eq_sym, Nat2Z.inj_mul).
          rewrite wordToB2_bwordToZ_step.
          replace (split1 2 sl wl) with WO~1~0
            by (erewrite <-split1_combine_existT; eauto).
          change (boothToZ (wencodeB2 WO~1~0)) with (-1)%Z.
          ring.
      
    - exists (rtrunc1 wl).
      exists (sext wu 1).
      split.
      + apply combine_wrshifta_rtrunc1_sext; auto.
      + econstructor.
        * reflexivity.
        * rewrite sext_wordToZ; eassumption.
        * rewrite <-H1.
          rewrite wordToB2_bwordToZ_step.
          replace (boothToZ (wencodeB2 (split1 2 sl wl))) with 0%Z.
          { replace (S sus + MultNumBitsExt + 1 - MultNumBitsExt - 1) with (S sus) by omega.
            replace (S sus + MultNumBitsExt - MultNumBitsExt - 1) with sus by omega.
            replace (Z.of_nat (pow2 (S sus))) with (Z.of_nat 2 * Z.of_nat (pow2 sus))%Z
              by (apply eq_sym, Nat2Z.inj_mul).
            ring.
          }
          { remember (split1 2 (MultBits - 2) w) as wt.
            replace (split1 2 sl wl) with wt
              by (subst; erewrite split1_combine_existT; eauto).
            do 3 dependent destruction wt.
            destruct b; destruct b0; intuition.
          }
  Qed.

  Lemma booth4Step_evalExpr_var:
    forall m_pos m_neg e,
      evalExpr (booth4Step m_pos m_neg (Var _ _ (evalExpr e))) =
      evalExpr (booth4Step m_pos m_neg e).
  Proof.
    intros; do 2 rewrite booth4Step_eval; reflexivity.
  Qed.

  Record BoothMultiplierInv (o: RegsT): Prop :=
    { bsiM : fullType type (SyntaxKind (Bit MultNumBitsExt));
      HbsiM : M.find "m" o = Some (existT _ _ bsiM);
      bsiR : fullType type (SyntaxKind (Bit MultNumBitsExt));
      HbsiR : M.find "r" o = Some (existT _ _ bsiR);

      bsiMp : fullType type (SyntaxKind (Bit MultBits));
      HbsiMp : M.find "m_pos" o = Some (existT _ _ bsiMp);
      bsiMn : fullType type (SyntaxKind (Bit MultBits));
      HbsiMn : M.find "m_neg" o = Some (existT _ _ bsiMn);

      bsiP : fullType type (SyntaxKind (Bit MultBits));
      HbsiP : M.find "p" o = Some (existT _ _ bsiP);

      bsiCnt : fullType type (SyntaxKind (Bit (S MultLogNumPhases)));
      HbsiCnt : M.find "cnt" o = Some (existT _ _ bsiCnt);

      HbsiMmp : bsiMp = extz (sext bsiM 1) (S MultNumBitsExt);
      HbsiMmn : bsiMn = extz (sext (wneg bsiM) 1) (S MultNumBitsExt);

      HbsiInv :
        exists sl (wl: word sl) sus su (wu: word su),
          sl = 8 * (wordToNat bsiCnt) + 1 /\
          su = S sus + MultNumBitsExt /\
          existT word _ bsiP = existT word _ (combine wl wu) /\
          BoothStepInv bsiM bsiR wl wu
    }.

  Ltac boothMultiplierInv_old :=
    repeat match goal with
           | [H: BoothMultiplierInv _ |- _] => destruct H
           end;
    kinv_red.

  Ltac boothMultiplierInv_new :=
    econstructor; (* let's prove that the invariant holds for the next state *)
    try (findReify; (reflexivity || eassumption); fail);
    kinv_red; (* unfolding invariant definitions *)
    repeat (* cheaper than "intuition" *)
      (match goal with
       | [ |- _ /\ _ ] => split
       end);
    try eassumption; intros; try reflexivity;
    intuition kinv_simpl; intuition idtac.

  Lemma boothMultiplierInv_ok':
    forall init n ll,
      init = initRegs (getRegInits boothMultiplierImpl) ->
      Multistep boothMultiplierImpl init n ll ->
      BoothMultiplierInv n.
  Proof.
    induction 2; intros.
 
    - boothMultiplierInv_old.
      unfold getRegInits, fst, boothMultiplierImpl, projT1.
      boothMultiplierInv_new.

      eexists; exists (natToWord 1 0).
      eexists; eexists; exists (natToWord (2 * MultNumBitsExt + 1) 0).
      split; [|split; [|split]].
      + reflexivity.
      + instantiate (1:= MultNumBitsExt); reflexivity.
      + reflexivity.
      + econstructor.
        * instantiate (1:= natToWord (2 * MultNumBitsExt) 0); reflexivity.
        * instantiate (1:= 0%Z); reflexivity.
        * reflexivity.

    - kinvert; [mred|mred| | |].
      + (* boothMultRegister *)
        Opaque natToWord evalExpr combine.
        kinv_action_dest.
        Transparent natToWord evalExpr.
        kinv_custom boothMultiplierInv_old.
        boothMultiplierInv_new.
        
        * simpl; unfold eq_rec; eq_rect_simpl.
          reflexivity.
        * simpl; unfold eq_rec; eq_rect_simpl.
          reflexivity.
        * simpl; unfold eq_rec; eq_rect_simpl.

          clear.
          set (extz (combine (x (Fin.FS Fin.F1)) (natToWord (MultNumBitsExt + 1) 0)) 1) as ww.
          pose proof (boothStepInv_init (x Fin.F1) (x (Fin.FS Fin.F1))) as Hinv0.
          eapply (boothStepInv_boothStep
                    (we:= Var type (SyntaxKind (Bit MultBits)) ww) (sus:= O)
                    eq_refl eq_refl eq_refl eq_refl) in Hinv0; [|reflexivity].
          simpl in Hinv0.
          destruct Hinv0 as [nwl [nwu [? ?]]].

          eexists; exists nwl.
          exists 1; eexists; exists nwu.

          repeat split.
          { subst ww.
            simpl; rewrite <-H.
            do 3 f_equal.
            { pose proof (wlshift_combine_sext_extz
                            (natToWord (S MultNumBitsExt) 0) (x Fin.F1) 1).
              simpl in H1; destruct_existT.
              match goal with
              | [H: @wlshift ?sz1 ?w1 ?n1 = _ |- @wlshift ?sz2 ?w2 ?n2 = _] =>
                change (@wlshift sz2 w2 n2) with (@wlshift sz1 w1 n1); rewrite H; clear H
              end.
              reflexivity.
            }
            { pose proof (wlshift_combine_sext_extz
                            (natToWord (S MultNumBitsExt) 0) (wneg (x Fin.F1)) 1).
              simpl in H1; destruct_existT.
              match goal with
              | [H: @wlshift ?sz1 ?w1 ?n1 = _ |- @wlshift ?sz2 ?w2 ?n2 = _] =>
                change (@wlshift sz2 w2 n2) with (@wlshift sz1 w1 n1); rewrite H; clear H
              end.
              reflexivity.
            }
          }
          { assumption. }
        
      + (* boothMultGetResult *)
        Opaque MultNumBits.
        kinv_action_dest.
        mred.
        Transparent MultNumBits.

      + (* boothStep *)
        kinv_action_dest.
        kinv_custom boothMultiplierInv_old.
        boothMultiplierInv_new.

        remember (8 * wordToNat x + 1) as psl.
        assert (psl >= 9)%nat.
        { subst; clear -n0.
          do 5 (dependent destruction x).
          destruct b, b0, b1, b2; cbn; try omega.
          elim n0; reflexivity.
        }
        do 9 (destruct psl as [|psl]; [omega|]); clear H.

        rename H12 into Hinv0.
        eapply (boothStepInv_booth4Step
                  (we:= Var type (SyntaxKind (Bit MultBits)) x2)
                  eq_refl eq_refl eq_refl eq_refl) in Hinv0; [|eassumption].
        replace (S x5 + MultNumBitsExt + 2)
          with ((S (S (S x5))) + MultNumBitsExt) in Hinv0 by omega.
        destruct Hinv0 as [nwl1 [nwu1 [Heq1 Hinv1]]].
        
        eapply (boothStepInv_booth4Step
                  eq_refl eq_refl eq_refl eq_refl) in Hinv1; [|eassumption].
        replace (S (S (S x5)) + MultNumBitsExt + 2)
          with (S (S (S (S (S x5)))) + MultNumBitsExt) in Hinv1 by omega.
        destruct Hinv1 as [nwl2 [nwu2 [Heq2 Hinv2]]].

        eapply (boothStepInv_booth4Step
                  eq_refl eq_refl eq_refl eq_refl) in Hinv2; [|eassumption].
        replace (S (S (S (S (S x5)))) + MultNumBitsExt + 2)
          with (S (S (S (S (S (S (S x5)))))) + MultNumBitsExt) in Hinv2 by omega.
        destruct Hinv2 as [nwl3 [nwu3 [Heq3 Hinv3]]].

        eapply (boothStepInv_booth4Step
                  eq_refl eq_refl eq_refl eq_refl) in Hinv3; [|eassumption].
        replace (S (S (S (S (S (S (S x5)))))) + MultNumBitsExt + 2)
          with (S (S (S (S (S (S (S (S (S x5)))))))) + MultNumBitsExt) in Hinv3 by omega.
        destruct Hinv3 as [nwl4 [nwu4 [Heq4 Hinv4]]].

        eexists; exists nwl4.
        eexists; eexists; exists nwu4.

        repeat split.
        * intros.
          match goal with
          | [ |- context [_ ^- ?w] ] =>
            replace w with (natToWord (S MultLogNumPhases) 1) by reflexivity
          end.
          rewrite <-wordToNat_natToWord_pred by assumption.
          omega.
        * rewrite booth4Step_evalExpr_var with (e:= booth4Step _ _ (#x2)%kami_expr).
          rewrite booth4Step_evalExpr_var with (e:= booth4Step _ _ (booth4Step _ _ _)).
          rewrite booth4Step_evalExpr_var.
          assumption.
        * assumption.
  Qed.

  Lemma boothMultiplierInv_ok:
    forall o,
      reachable o boothMultiplierImpl ->
      BoothMultiplierInv o.
  Proof.
    intros; inv H; inv H0.
    eapply boothMultiplierInv_ok'; eauto.
  Qed.
  
  Local Definition thetaR (ir sr: RegsT): Prop.
  Proof.
    kexistv "m_pos" m_pos ir (Bit MultBits).
    kexistv "m_neg" m_neg ir (Bit MultBits).
    kexistv "p" p ir (Bit MultBits).
    kexistv "m" m ir (Bit MultNumBitsExt).
    kexistv "r" r ir (Bit MultNumBitsExt).
    kexistv "cnt" cnt ir (Bit (S MultLogNumPhases)).

    exact (sr = ["r" <- existT _ _ r]
                +["m" <- existT _ _ m])%fmap.
  Defined.
  Hint Unfold thetaR: MapDefs.

  Local Notation "'_STRUCT_'" := (fun i : Fin.t _ => _).

  Theorem multiplier_ok: boothMultiplierImpl <<== multiplierSpec.
  Proof.
    kdecomposeR_nodefs thetaR.
    kinv_add boothMultiplierInv_ok.
    kinvert.

    - (* "boothMultRegister" |-> "multRegister" *)
      Opaque natToWord evalExpr combine.
      kinv_action_dest.
      kinv_custom boothMultiplierInv_old.
      kinv_regmap_red.
      eexists; exists (Some "multRegister"); split; kinv_constr.
      kinv_eq.
      Transparent natToWord evalExpr combine.

    - (* "boothMultGetResult" |-> "multGetResult" *)
      Opaque MultNumBits.
      kinv_action_dest.
      kinv_custom boothMultiplierInv_old.
      kinv_regmap_red.
      Transparent MultNumBits.

      eexists; exists (Some "multGetResult"); split; kinv_constr.
      apply boothStepInv_finish in H6; dest.
      assert (x3 = MultNumBitsExt) by (apply eq_sigT_fst in H5; cbn; cbn in H5; omega).
      subst; destruct_existT.
      rewrite idElementwiseId; unfold id.
      repeat f_equal.
      apply pair_eq; [|reflexivity].
      fin_func_eq.

      + Opaque split1 split2 wordToZ.
        simpl.
        unfold eq_rec_r, eq_rec; repeat rewrite <-eq_rect_eq.
        repeat f_equal.
        rewrite wtl_combine.
        unfold wmultZ, wordBinZ.
        pose proof (sext_wordToZ bsiM 65).
        cbn; cbn in H1; rewrite H1.
        pose proof (sext_wordToZ bsiR 65).
        cbn; cbn in H2; rewrite H2.
        cbn in H0; rewrite <-H0.
        assert (x = 2 * MultNumBitsExt) by (apply eq_sigT_fst in H; omega); subst.
        destruct_existT.
        pose proof (sext_wordToZ x4 1); cbn; cbn in H; rewrite H.
        rewrite sext_split1.
        rewrite ZToWord_wordToZ.
        reflexivity.
        Transparent split1 split2 wordToZ.

      + Opaque split1 split2 wordToZ.
        simpl.
        unfold eq_rec_r, eq_rec; repeat rewrite <-eq_rect_eq.
        repeat f_equal.
        rewrite wtl_combine.
        unfold wmultZ, wordBinZ.
        pose proof (sext_wordToZ bsiM 65).
        cbn; cbn in H1; rewrite H1.
        pose proof (sext_wordToZ bsiR 65).
        cbn; cbn in H2; rewrite H2.
        cbn in H0; rewrite <-H0.
        assert (x = 2 * MultNumBitsExt) by (apply eq_sigT_fst in H; omega); subst.
        destruct_existT.
        pose proof (sext_wordToZ x4 1); cbn; cbn in H; rewrite H.
        rewrite sext_split1.
        rewrite ZToWord_wordToZ.
        reflexivity.
        Transparent split1 split2 wordToZ.

    - (* "boothStep" |-> . *)
      kinv_action_dest.
      kinv_custom boothMultiplierInv_old.
      kinv_regmap_red.
      eexists; exists None; split; kinv_constr.
      
  Qed.

End Multiplier64.


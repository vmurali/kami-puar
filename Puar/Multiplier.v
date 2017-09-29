Require Import Kami.
Require Import Lib.NatLib Lib.Indexer Lib.Struct Lib.FMap Lib.Reflection.
Require Import Kami.Tactics Kami.SemFacts Kami.StepDet.
Require Import Puar.Useful FunctionalExtensionality.

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

  Lemma booth4Step_eval:
    forall m_pos m_neg p,
      evalExpr (booth4Step m_pos m_neg p) =
      wrshifta
        (if weq (split1 3 (MultBits - 3) (evalExpr p)) WO~0~0~1
         then evalExpr p ^+ m_pos
         else
           if weq (split1 3 (MultBits - 3) (evalExpr p)) WO~0~1~0
           then evalExpr p ^+ m_pos
           else
             if weq (split1 3 (MultBits - 3) (evalExpr p)) WO~0~1~1
             then evalExpr p ^+ (wlshift m_pos 1)
             else
               if weq (split1 3 (MultBits - 3) (evalExpr p)) WO~1~0~0
               then evalExpr p ^+ (wlshift m_neg 1)
               else
                 if weq (split1 3 (MultBits - 3) (evalExpr p)) WO~1~0~1
                 then evalExpr p ^+ m_neg
                 else
                   if weq (split1 3 (MultBits - 3) (evalExpr p)) WO~1~1~0
                   then evalExpr p ^+ m_neg
                   else evalExpr p) 2.
  Proof.
    intros; unfold booth4Step.
    unfold evalExpr; fold evalExpr.
    unfold evalBinBit.
    rewrite booth4Step'_eval.

    repeat destruct (weq _ _); try reflexivity.
  Qed.
  
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
      with Register "om" : Bit MultNumBitsExt <- Default
      with Register "or" : Bit MultNumBitsExt <- Default
      with Register "cnt" : Bit (S MultLogNumPhases) <- Default

      with Rule "boothMultRegister" :=
        Call src <- multPull();

        LET om : Bit (pred MultNumBitsExt + 1) <- #src!MultInStr@."multiplicand";
        LET om_neg <- (UniBit (Inv _) #om) + $1;

        LET m_pos : Bit MultBits <-
          BinBit (Concat _ (S (S MultNumBitsExt))) #om $0;
        LET m_neg : Bit MultBits <-
          BinBit (Concat _ (S (S MultNumBitsExt))) #om_neg $0;

        LET r <- #src!MultInStr@."multiplier";
        LET p : Bit MultBits <-
          BinBit (Concat (S MultNumBitsExt) _) $0 (BinBit (Concat _ 1) #r $0);

        Write "om" <- #om;
        Write "or" <- #r;
        
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

    Definition rtrunc1 sz (w: word (S sz)): word sz:=
      match w with
      | WO => idProp
      | WS _ w' => w'
      end.

    Definition rtrunc2 sz (w: word (S (S sz))): word sz :=
      match w with
      | WO => idProp
      | WS _ w' =>
        match w' with
        | WO => idProp
        | WS _ w'' => w''
        end
      end.

    Definition wlsb sz (w: word (S sz)) :=
      match w with
      | WO => idProp
      | WS b _ => b
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

    Eval vm_compute in (bwordToZ (wordToB4 WO~1~1~0~1~0)).

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
  | BSInv: forall sl su (wl: word (S sl)) (wu: word su) u,
      wordToZ wu = (wordToZ m * u)%Z ->
      (u + bwordToZ (wordToB2 wl) * Z.of_nat (pow2 (su - sz - 1)))%Z = wordToZ p ->
      BoothStepInv m p wl wu.

  Lemma boothStepInv_inv:
    forall {sz} (m p: word sz) sl su (wl: word (S sl)) (wu: word su),
      BoothStepInv m p wl wu ->
      exists u,
        wordToZ wu = (wordToZ m * u)%Z /\
        (u + bwordToZ (wordToB2 wl) * Z.of_nat (pow2 (su - sz - 1)))%Z = wordToZ p.
  Proof.
    intros.
    inv H; destruct_existT.
    exists u.
    split; assumption.
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

  Lemma wordToZ_wzero':
    forall sz, wordToZ (wzero' sz) = 0%Z.
  Proof.
  Admitted.

  Lemma boothStepInv_init:
    forall sz m p,
      BoothStepInv m (p: word sz)
                   (combine (natToWord 1 0) p)
                   (natToWord (S sz) 0).
  Proof.
    intros; econstructor; try reflexivity.
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
      wordToZ wu = (wordToZ m * wordToZ p)%Z.
  Proof.
    intros.
    apply boothStepInv_inv in H; dest.

    rewrite wordToB2_one in H0.
    rewrite Z.add_0_r in H0; subst.
    assumption.
  Qed.

  Definition extz {sz} (w: word sz) (n: nat) := combine (wzero n) w.

  Lemma combine_wplus:
    forall sl (w1: word sl) su (w2 w3: word su),
      combine w1 (w2 ^+ w3) = combine w1 w2 ^+ extz w3 sl.
  Proof.
  Admitted.

  Lemma existT_wplus:
    forall sz (w1 w2: word sz) sz' (w3 w4: word sz'),
      existT word _ w1 = existT word _ w3 ->
      existT word _ w2 = existT word _ w4 ->
      existT word _ (w1 ^+ w2) = existT word _ (w3 ^+ w4).
  Proof.
    intros.
    rewrite eq_sigT_sig_eq in H; destruct H as [Hsz1 ?].
    rewrite eq_sigT_sig_eq in H0; destruct H0 as [Hsz2 ?].
    subst; do 2 rewrite <-eq_rect_eq.
    reflexivity.
  Qed.

  Lemma wrshifta_wplus:
    forall sz (w1 w2: word sz) n,
      wrshifta (w1 ^+ w2) n = wrshifta w1 n ^+ wrshifta w2 n.
  Proof.
  Admitted.

  Lemma combine_wrshifta_rtrunc1_sext:
    forall s (w: word s) sl (wl: word (S (S sl))) su (wu: word su),
      existT word s w =
      existT word ((S (S sl)) + su) (combine wl wu) ->
      existT word s (wrshifta w 1) =
      existT word ((S sl) + (su + 1)) (combine (rtrunc1 wl) (sext wu 1)).
  Proof.
  Admitted.

  Lemma combine_wrshifta_rtrunc2_sext:
    forall s (w: word s) sl (wl: word (S (S (S sl)))) su (wu: word su),
      existT word s w =
      existT word ((S (S (S sl))) + su) (combine wl wu) ->
      existT word s (wrshifta w 2) =
      existT word ((S sl) + (su + 2)) (combine (rtrunc2 wl) (sext wu 2)).
  Proof.
  Admitted.

  Lemma wrshifta_extz_sext:
    forall sz (w: word sz) n1 n2,
      existT word _ (wrshifta (extz w (n1 + n2)) n1) =
      existT word _ (sext (extz w n2) n1).
  Proof.
  Admitted.

  Lemma extz_sext:
    forall sz (w: word sz) n1 n2,
      existT word _ (extz (sext w n1) n2) =
      existT word _ (sext (extz w n2) n1).
  Proof.
  Admitted.

  Lemma extz_sext_eq_rect:
    forall sz (w: word sz) n1 n2 nsz Hnsz1,
    exists Hnsz2,
      eq_rect (n2 + (sz + n1)) word (extz (sext w n1) n2) nsz Hnsz1 =
      eq_rect (n2 + sz + n1) word (sext (extz w n2) n1) nsz Hnsz2.
  Proof.
    intros; subst; simpl.
    assert (Hsz: n2 + sz + n1 = n2 + (sz + n1)) by omega.
    exists Hsz.
    pose proof (extz_sext w n1 n2).
    pose proof (eq_sigT_snd H).
    rewrite <-H0.
    eq_rect_simpl.
    reflexivity.
  Qed.

  Lemma existT_sext:
    forall sz1 (w1: word sz1) sz2 (w2: word sz2) n,
      existT word _ w1 = existT word _ w2 ->
      existT word _ (sext w1 n) = existT word _ (sext w2 n).
  Proof.
    intros; inv H; reflexivity.
  Qed.

  Lemma existT_extz:
    forall sz1 (w1: word sz1) sz2 (w2: word sz2) n,
      existT word _ w1 = existT word _ w2 ->
      existT word _ (extz w1 n) = existT word _ (extz w2 n).
  Proof.
    intros; inv H; reflexivity.
  Qed.

  Lemma extz_extz:
    forall sz (w: word sz) n1 n2,
      existT word _ (extz (extz w n1) n2) =
      existT word _ (extz w (n2 + n1)).
  Proof.
  Admitted.

  Lemma sext_wplus_wordToZ_distr:
    forall sz (w1 w2: word sz) n,
      n <> 0 -> wordToZ (sext w1 n ^+ sext w2 n) =
                (wordToZ (sext w1 n) + wordToZ (sext w2 n))%Z.
  Proof.
  Admitted.

  Lemma sext_wordToZ:
    forall sz (w: word sz) n,
      wordToZ (sext w n) = wordToZ w.
  Proof.
  Admitted.

  Lemma split1_combine_existT:
    forall sz n (w: word (n + sz)) sl (wl: word (n + sl)) su (wu: word su),
      existT word _ w = existT word _ (combine wl wu) ->
      split1 n _ w = split1 n _ wl.
  Proof.
  Admitted.

  Lemma extz_pow2_wordToZ:
    forall sz (w: word sz) n,
      wordToZ (extz w n) = (wordToZ w * Z.of_nat (pow2 n))%Z.
  Proof.
  Admitted.

  Lemma extz_wneg:
    forall sz (w: word sz) n,
      extz (wneg w) n = wneg (extz w n).
  Proof.
  Admitted.

  Lemma wneg_wordToZ:
    forall sz (w: word sz) z,
      (z + wordToZ (wneg w))%Z = (z - wordToZ w)%Z.
  Proof.
  Admitted.

  Lemma existT_eq_rect:
    forall (X: Type) (P: X -> Type) (x1 x2: X) (H1: P x1) (Hx: x1 = x2),
      existT P x2 (eq_rect x1 P H1 x2 Hx) =
      existT P x1 H1.
  Proof.
    intros; subst.
    rewrite <-eq_rect_eq; reflexivity.
  Qed.

  Lemma sext_eq_rect:
    forall sz (w: word sz) n nsz Hsz1,
    exists Hsz2,
      eq_rect (sz + n) word (sext w n) (nsz + n) Hsz1 =
      sext (eq_rect sz word w nsz Hsz2) n.
  Proof.
    intros.
    assert (Hsz: sz = nsz) by omega.
    exists Hsz.
    subst; simpl.
    eq_rect_simpl.
    reflexivity.
  Qed.

  Lemma wordToZ_eq_rect:
    forall sz (w: word sz) nsz Hsz,
      wordToZ (eq_rect _ word w nsz Hsz) = wordToZ w.
  Proof.
    intros; subst; simpl; reflexivity.
  Qed.

  Lemma pow2_S_z:
    forall n, Z.of_nat (pow2 (S n)) = (2 * Z.of_nat (pow2 n))%Z.
  Proof.
    intros.
    replace (2 * Z.of_nat (pow2 n))%Z with
        (Z.of_nat (pow2 n) + Z.of_nat (pow2 n))%Z by omega.
    simpl.
    repeat rewrite Nat2Z.inj_add.
    ring.
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
    rewrite booth4Step_eval.
    remember (evalExpr we) as w; clear Heqw we.
    repeat destruct (weq _ _).

    - exists (rtrunc2 wl).
      assert (Hsu: sus + (MultNumBitsExt + 1 + 2) = S sus + MultNumBitsExt + 2)
        by omega.
      exists (sext wu 2 ^+ (eq_rect _ word (extz (sext (sext m 1) 2) sus) _ Hsu)).
      split.

      + rewrite wrshifta_wplus.
        rewrite combine_wplus.
        apply existT_wplus.
        * apply combine_wrshifta_rtrunc2_sext; auto.
        * apply eq_sigT_fst in H3.
          change (S MultNumBitsExt) with (2 + (MultNumBitsExt - 1)).
          change (MultBits - 3 + 3) with
              (2 + (MultNumBitsExt - 1) + (S MultNumBitsExt)).
          rewrite wrshifta_extz_sext.
          rewrite <-extz_sext.
          replace (MultNumBitsExt - 1) with (S sl + (MultNumBitsExt - 1 - (S sl)))
            by admit.
          rewrite <-extz_extz.
          apply existT_extz.
          rewrite existT_eq_rect.
          replace (MultNumBitsExt - 1 - S sl) with sus; [reflexivity|].
          assert (S (S (S sl)) + sus = MultBits - MultNumBitsExt - 1) by omega.
          simpl in H1; assert (S (sl + sus) = 64) by omega.
          apply eq_sym, Nat.add_sub_eq_l.
          simpl; rewrite H2; reflexivity.
      + eapply BSInv with (u0:= (u + Z.of_nat (pow2 sus))%Z).
        * pose proof (extz_sext_eq_rect (sext m 1) 2 sus Hsu).
          destruct H1 as [Hsu' ?].
          rewrite H1.
          pose proof (sext_eq_rect (extz (sext m 1) sus) 2 _ Hsu').
          destruct H2 as [Hsu'' ?].
          rewrite H2.
          rewrite sext_wplus_wordToZ_distr by discriminate.
          rewrite Z.mul_add_distr_l, <-H.
          do 2 rewrite sext_wordToZ.
          rewrite wordToZ_eq_rect.
          rewrite extz_pow2_wordToZ.
          rewrite sext_wordToZ.
          reflexivity.
        * rewrite wordToB2_wordToB4.
          rewrite <-H0, <-Z.add_assoc.
          replace (S sus + MultNumBitsExt + 2 - MultNumBitsExt - 1)
            with (S (S sus)) by omega.
          apply Z.add_cancel_l.
          replace (S sus + MultNumBitsExt - MultNumBitsExt - 1) with sus by omega.
          rewrite wordToB4_bwordToZ_step.
          replace (split1 3 sl wl) with (WO~0~0~1)
            by (erewrite <-split1_combine_existT; eauto).
          change (bbToZ (wencodeB4 WO~0~0~1)) with 1%Z.
          rewrite Z.mul_add_distr_r.
          rewrite Z.add_comm.
          f_equal; [|omega].
          replace (Z.of_nat (pow2 (S (S sus)))) with (4 * Z.of_nat (pow2 sus))%Z
            by (do 2 rewrite pow2_S_z; ring).
          rewrite Z.mul_assoc; f_equal; omega.

    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
  Admitted.

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
          (* NOTE: [omega] can't solve this :( *)
          clear -H3; apply eq_sigT_fst in H3.
          assert (MultBits - 2 = sl + (S sus + MultNumBitsExt)) by omega.
          rewrite Nat.add_assoc in H.
          assert (MultBits - 2 - MultNumBitsExt = sl + S sus) by omega.
          simpl; rewrite <-H0; reflexivity.
      + eapply BSInv with (u0:= (u + Z.of_nat (pow2 (S sus)))%Z).
        * rewrite Z.mul_add_distr_l, <-H.
          rewrite sext_wplus_wordToZ_distr by discriminate.
          f_equal.
          { apply sext_wordToZ. }
          { rewrite sext_wordToZ.
            apply extz_pow2_wordToZ.
          }
        * rewrite <-H0, <-Z.add_assoc.
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
          assert (MultBits - 2 = sl + (S sus + MultNumBitsExt)) by omega.
          rewrite Nat.add_assoc in H.
          assert (MultBits - 2 - MultNumBitsExt = sl + S sus) by omega.
          simpl; rewrite <-H0; reflexivity.
      + eapply BSInv with (u0:= (u - Z.of_nat (pow2 (S sus)))%Z).
        * rewrite Z.mul_sub_distr_l, <-H.
          rewrite sext_wplus_wordToZ_distr by discriminate.
          do 2 rewrite sext_wordToZ.
          rewrite extz_wneg.
          rewrite wneg_wordToZ.
          f_equal.
          apply extz_pow2_wordToZ.
        * rewrite <-H0.
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
        * rewrite sext_wordToZ; eassumption.
        * rewrite <-H0.
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

  Record BoothMultiplierInv (o: RegsT): Prop :=
    { bsiOm : fullType type (SyntaxKind (Bit MultNumBitsExt));
      HbsiOm : M.find "om" o = Some (existT _ _ bsiOm);
      bsiOr : fullType type (SyntaxKind (Bit MultNumBitsExt));
      HbsiOr : M.find "or" o = Some (existT _ _ bsiOr);

      bsiMp : fullType type (SyntaxKind (Bit MultBits));
      HbsiMp : M.find "m_pos" o = Some (existT _ _ bsiMp);
      bsiMn : fullType type (SyntaxKind (Bit MultBits));
      HbsiMn : M.find "m_neg" o = Some (existT _ _ bsiMn);

      bsiP : fullType type (SyntaxKind (Bit MultBits));
      HbsiP : M.find "p" o = Some (existT _ _ bsiP);

      HbsiMmp : bsiMp = extz bsiOm (S (S MultNumBitsExt));
      HbsiMmn : bsiMn = extz (wneg bsiOm) (S (S MultNumBitsExt));

      HbsiInv : exists sl (wl: word sl) su (wu: word su),
          existT word _ bsiP = existT word _ (combine wl wu) /\
          BoothStepInv bsiOm bsiOr wl wu
          
    }.

  Ltac boothMultiplierInv_old :=
    repeat match goal with
           | [H: BoothMultiplierInv _ |- _] => destruct H
           end;
    kinv_red.

  Ltac boothMultiplierInv_new :=
    econstructor; (* let's prove that the invariant holds for the next state *)
    try (findReify; (reflexivity || eassumption); fail);
    kregmap_clear; (* for improving performance *)
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

      admit.

    - kinvert.
      + mred.
      + mred.
      + admit.
      + admit.
      + admit.
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


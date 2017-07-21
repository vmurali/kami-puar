Require Import Kami.
Require Import Lib.Indexer Lib.Struct Lib.FMap Lib.Reflection.
Require Import Kami.Tactics Kami.SemFacts.
Require Import Puar.Useful Puar.Processor FunctionalExtensionality.

(* Below implements a radix-4 Booth Multiplier. *)
Section Multiplier64.
  (* NOTE: hard to declare [LogNumPhases] and [NumBitsPerPhase] as variables,
   * since truncation and extension require certain equation w.r.t. bit-lengths.
   *)
  (* Variable MultLogNumPhases MultNumBitsPerPhase: nat. *)
  Definition MultLogNumPhases := 3.
  Definition MultNumBitsPerPhase := 8.

  Local Definition MultNumPhases := wordToNat (wones MultLogNumPhases) + 1.
  Local Definition MultNumBits := MultNumPhases * MultNumBitsPerPhase.
  Local Definition MultBits := 2 * MultNumBits + 2.

  Definition MultInStr := STRUCT { "multiplicand" :: Bit MultNumBits;
                                   "multiplier" :: Bit MultNumBits }.
  Definition MultOutStr := STRUCT { "high" :: Bit MultNumBits;
                                    "low" :: Bit MultNumBits }.

  Definition multRegister := MethodSig "multRegister"(Struct MultInStr): Void.
  Definition multGetResult := MethodSig "multGetResult"(Void): Struct MultOutStr.

  Definition boothStep' {ty}
             (m_pos m_neg: fullType ty (SyntaxKind (Bit MultBits)))
             (p: Expr ty (SyntaxKind (Bit MultBits)))
             (pr: Expr ty (SyntaxKind (Bit 3))) :=
    (IF (pr == $$(WO~0~0~0)) then p
     else IF (pr == $$(WO~0~0~1)) then p + #m_pos
     else IF (pr == $$(WO~0~1~0)) then p + #m_pos
     else IF (pr == $$(WO~0~1~1)) then p + (#m_pos << $$(WO~1))
     else IF (pr == $$(WO~1~0~0)) then p + (#m_pos << $$(WO~1))
     else IF (pr == $$(WO~1~0~1)) then p + #m_neg
     else IF (pr == $$(WO~1~1~0)) then p + #m_neg
     else p)%kami_expr.

  Definition boothStep {ty}
             (m_pos m_neg: fullType ty (SyntaxKind (Bit MultBits)))
             (p: Expr ty (SyntaxKind (Bit ((MultBits - 3) + 3))))
    : Expr ty (SyntaxKind (Bit MultBits)) :=
    (boothStep' m_pos m_neg p (UniBit (Trunc 3 _) p) >> $$(WO~1~0))%kami_expr.

  Fixpoint boothSteps (cnt: nat)
           {ty} (m_pos m_neg: fullType ty (SyntaxKind (Bit MultBits)))
           (p: fullType ty (SyntaxKind (Bit ((MultBits - 3) + 3))))
           (cont: fullType ty (SyntaxKind (Bit ((MultBits - 3) + 3))) ->
                  ActionT ty Void)
    : ActionT ty Void :=
    match cnt with
    | O => (cont p)%kami_action
    | S n => (LET np <- boothStep m_pos m_neg #p;
              boothSteps n m_pos m_neg np cont)%kami_action
    end.

  Definition boothMultiplierImpl :=
    MODULE {
      Register "m_pos" : Bit MultBits <- Default
      with Register "m_neg" : Bit MultBits <- Default
      with Register "p" : Bit MultBits <- Default
      with Register "cnt" : Bit (S MultLogNumPhases) <- Default

      with Method "multRegister"(src: Struct MultInStr): Void :=
        LET m : Bit (pred MultNumBits + 1) <- #src!MultInStr@."multiplicand";
        LET m_msb <- UniBit (TruncLsb _ 1) #m;
        LET m_neg <- (UniBit (Inv _) #m) + $1;
        LET m_neg_msb <- UniBit (TruncLsb _ 1) #m_neg;
        
        Write "m_pos" : Bit MultBits <-
          BinBit (Concat _ (S MultNumBits)) (BinBit (Concat _ _) #m_msb #m) $0;
        Write "m_neg" : Bit MultBits <-
          BinBit (Concat _ (S MultNumBits)) (BinBit (Concat _ _) #m_neg_msb #m_neg) $0;
        
        LET r <- #src!MultInStr@."multiplier";
        Write "p" : Bit MultBits <-
          BinBit (Concat (S MultNumBits) _) $0 (BinBit (Concat _ 1) #r $0);

        Write "cnt" : Bit (S MultLogNumPhases) <- $(MultNumPhases);
        Retv

      with Method "multGetResult"(): Struct MultOutStr :=
        Read cnt : Bit MultLogNumPhases <- "cnt";
        Assert (#cnt == $0);

        Read p : Bit MultBits <- "p";
        LET high : Bit MultNumBits <- UniBit (ConstExtract (S MultNumBits) MultNumBits 1) #p;
        LET low : Bit MultNumBits <- UniBit (ConstExtract 1 MultNumBits (S MultNumBits)) #p;

        LET ret : Struct MultOutStr <- STRUCT { "high" ::= $$Default; "low" ::= #low };
        Ret #ret
            
      with Rule "boothStep" :=
        Read cnt : Bit MultLogNumPhases <- "cnt";
        Assert (#cnt != $0);

        Read m_pos : Bit MultBits <- "m_pos";
        Read m_neg : Bit MultBits <- "m_neg";
        Read p : Bit MultBits <- "p";

        boothSteps
          MultNumBitsPerPhase m_pos m_neg p
          (fun np => Write "p" <- #np; Retv)
    }.

  Definition multiplierSpec :=
    MODULE {
      Register "p" : Bit (2 * MultNumBits) <- Default

      with Method "multRegister"(src: Struct MultInStr): Void :=
        LET m : Bit MultNumBits <- #src!MultInStr@."multiplicand";
        LET m_ext : Bit (2 * MultNumBits) <- UniBit (SignExtendTrunc _ _) #m;
        LET r : Bit MultNumBits <- #src!MultInStr@."multiplier";
        LET r_ext : Bit (2 * MultNumBits) <- UniBit (SignExtendTrunc _ _) #m;

        Write "p" <- #m_ext *s #r_ext;
        Retv

      with Method "multGetResult"(): Struct MultOutStr :=
        Read p : Bit (MultNumBits + MultNumBits) <- "p";
        LET high : Bit MultNumBits <- UniBit (TruncLsb _ _) #p;
        LET low : Bit MultNumBits <- UniBit (Trunc _ _) #p;

        LET ret : Struct MultOutStr <- STRUCT { "high" ::= #high; "low" ::= #low };
        Ret #ret
    }.

End Multiplier64.

(* Below implements non-restoring division for unsigned integers.
 * Operand signs are re-applied after the division.
 * NOTE: the rule for operand signs:
 * when "z = d * q + r", we have "sign(r) = sign(z)" and "|r| < |d|".
 *)
Section Divider64.
  Definition DivLogNumPhases := 3.
  Definition DivNumBitsPerPhase := 8.

  Local Definition DivNumPhases := wordToNat (wones DivLogNumPhases) + 1.
  Local Definition DivNumBits := DivNumPhases * DivNumBitsPerPhase.
  Local Definition DivBits := 2 * DivNumBits + 2.

  Definition DivInStr := STRUCT { "dividend" :: Bit DivNumBits;
                                  "divisor" :: Bit DivNumBits }.
  Definition DivOutStr := STRUCT { "quotient" :: Bit DivNumBits;
                                   "remainder" :: Bit DivNumBits }.

  Definition divRegister := MethodSig "divRegister"(Struct DivInStr): Void.
  Definition divGetResult := MethodSig "divGetResult"(Void): Struct DivOutStr.

  (*! TODO: optimize this step !*)
  Definition divStep {ty}
             (pq: fullType ty (SyntaxKind (Bit (DivNumBits + S DivNumBits))))
             (dr: fullType ty (SyntaxKind (Bit DivNumBits)))
    : Expr ty (SyntaxKind (Bit (DivNumBits + S DivNumBits))) :=
    ((* Step 1: shift *)
      let pq_shift := BinBit (Sll ((DivNumBits + DivNumBits) + 1) _) #pq $$(natToWord 1 1) in
      (* Step 2: add or subtract *)
      let pq_shift_msb := UniBit (TruncLsb _ 1) pq_shift in
      let pq_shift_p := (IF (pq_shift_msb == $0)
                         then pq_shift - (BinBit (Concat _ (S DivNumBits)) #dr $0)
                         else pq_shift + (BinBit (Concat _ (S DivNumBits)) #dr $0)) in
      (* Step 3: set the quotient bit, which is LSB here *)
      let pq_shift_p_msb := UniBit (TruncLsb _ 1) pq_shift_p in
      IF (pq_shift_p_msb == $0)
      then pq_shift_p + $1
      else pq_shift_p
    )%kami_expr.
  
  Fixpoint divSteps (cnt: nat)
           {ty} (pq: fullType ty (SyntaxKind (Bit (DivNumBits + S DivNumBits))))
           (dr: fullType ty (SyntaxKind (Bit DivNumBits)))
           (cont: fullType ty (SyntaxKind (Bit (DivNumBits + S DivNumBits))) ->
                  ActionT ty Void)
    : ActionT ty Void :=
    match cnt with
    | O => (cont pq)%kami_action
    | S n => (LET npq <- divStep pq dr;
              divSteps n npq dr cont)%kami_action
    end.

  Definition nrDividerImpl :=
    MODULE {
      Register "pq" : Bit (DivNumBits + S DivNumBits) <- Default
      with Register "dr" : Bit DivNumBits <- Default
      with Register "cnt" : Bit (S DivLogNumPhases) <- Default

      with Method "divRegister"(src: Struct DivInStr): Void :=
        LET dividend : Bit DivNumBits <- #src!DivInStr@."dividend";
        LET divisor : Bit DivNumBits <- #src!DivInStr@."divisor";

        Write "pq" : Bit (DivNumBits + S DivNumBits) <- UniBit (ZeroExtendTrunc _ _) #dividend;
        Write "dr" <- #divisor;
        Write "cnt" : Bit (S DivLogNumPhases) <- $(DivNumPhases);
        Retv

      with Method "divGetResult"(): Struct DivOutStr :=
        Read cnt : Bit DivLogNumPhases <- "cnt";
        Assert (#cnt == $0);

        Read pq : Bit (DivNumBits + S DivNumBits) <- "pq";
        Read dr : Bit DivNumBits <- "dr";
        
        LET p : Bit (DivNumBits + 1) <- UniBit (TruncLsb _ _) #pq;
        LET q : Bit DivNumBits <- UniBit (Trunc _ _) #pq;

        LET p_msb <- UniBit (TruncLsb _ 1) #p;
        LET p_ls : Bit DivNumBits <- UniBit (Trunc _ _) #p;
        LET rem : Bit DivNumBits <- (IF (#p_msb == $0)
                                     then #p_ls
                                     else #p_ls + #dr);
        
        LET ret : Struct DivOutStr <- STRUCT { "quotient" ::= #q;
                                               "remainder" ::= #rem
                                             };
        Ret #ret
            
      with Rule "divStep" :=
        Read cnt : Bit DivLogNumPhases <- "cnt";
        Assert (#cnt != $0);

        Read pq : Bit (DivNumBits + S DivNumBits) <- "pq";
        Read dr : Bit DivNumBits <- "dr";
        
        divSteps
          DivNumBitsPerPhase pq dr
          (fun npq => Write "pq" <- #npq; Retv)
    }.

  Definition dividerSpec :=
    MODULE {
      Register "quotient" : Bit DivNumBits <- Default
      with Register "remainder" : Bit DivNumBits <- Default
                         
      with Method "DivRegister"(src: Struct DivInStr): Void :=
        LET m : Bit DivNumBits <- #src!DivInStr@."dividend";
        LET r : Bit DivNumBits <- #src!DivInStr@."divisor";

        Write "quotient" <- #m /s #r;
        Write "remainder" <- BinBit (Rem _ SignSS) #m #r;
        Retv

      with Method "DivGetResult"(): Struct DivOutStr :=
        Read quotient : Bit DivNumBits <- "quotient";
        Read remainder : Bit DivNumBits <- "remainder";

        LET ret : Struct DivOutStr <- STRUCT { "quotient" ::= #quotient;
                                               "remainder" ::= #remainder };
        Ret #ret
    }.
  
End Divider64.

Section Processor.
  Variable NumDataBytes: nat.
  Variables VAddr PAddr Inst Mode MemException ExecException: Kind.

  Variable isNotLongLat: forall ty, ty Inst -> Bool @ ty.
  
  Variable isMul: forall ty, ty Inst -> Bool @ ty.
  Variable isDiv: forall ty, ty Inst -> Bool @ ty.
  Variable isRem: forall ty, ty Inst -> Bool @ ty.

  Definition MulDivSign := Bit 2.
  Definition MulDivSignSS : ConstT MulDivSign := WO~0~0.
  Definition MulDivSignSU : ConstT MulDivSign := WO~0~1.
  Definition MulDivSignUU : ConstT MulDivSign := WO~1~0.
  Variable getMulDivSign: forall ty, ty Inst -> MulDivSign @ ty.

  Local Notation Exec := (Exec NumDataBytes VAddr ExecException).

  Section Spec.

    Definition Data := Bit (8 * NumDataBytes).

    Definition execFnLongLatSpec ty (pc: ty VAddr)
               (inst: ty Inst) (val1 val2: ty Data)
      : (Struct Exec) @ ty.
    Proof.
      refine (STRUCT { "data" ::= _;
                       "memVAddr" ::= $$Default;
                       "exception" ::= $$Default;
                       "nextPc" ::= $$Default (* (pc + 4)? *) })%kami_expr.
      refine (IF (isMul _ inst)
              then _
              else (IF (isDiv _ inst)
                    then _
                    else (IF (isRem _ inst)
                          then _
                          else $$Default)))%kami_expr.
      - refine (IF (getMulDivSign _ inst == $$MulDivSignSS)
                then #val1 *s #val2
                else (IF (getMulDivSign _ inst == $$MulDivSignSU)
                      then #val1 *su #val2
                      else #val1 * #val2))%kami_expr.
      - refine (IF (getMulDivSign _ inst == $$MulDivSignSS)
                then #val1 /s #val2
                else (IF (getMulDivSign _ inst == $$MulDivSignSU)
                      then #val1 /su #val2
                      else #val1 / #val2))%kami_expr.
      - refine (IF (getMulDivSign _ inst == $$MulDivSignSS)
                then BinBit (Rem _ SignSS) #val1 #val2
                else (IF (getMulDivSign _ inst == $$MulDivSignSU)
                      then BinBit (Rem _ SignSU) #val1 #val2
                      else BinBit (Rem _ SignUU) #val1 #val2))%kami_expr.
    Defined.

    Definition longLatSpec :=
      getModFromSin (@LongLatency
                       NumDataBytes VAddr PAddr Inst Mode MemException ExecException
                       isNotLongLat execFnLongLatSpec).

  End Spec.

  Section Impl.

    Local Notation regReadFirst := (regReadFirst NumDataBytes VAddr PAddr Inst Mode MemException).
    Local Notation regReadPop := (regReadPop NumDataBytes VAddr PAddr Inst Mode MemException).
    Local Notation RegReadT := (RegReadT NumDataBytes VAddr PAddr Inst Mode MemException).
    Local Notation execEnq := (execEnq NumDataBytes VAddr PAddr Inst Mode
                                       MemException ExecException).

    Definition LongLatStr := STRUCT { "inst" :: Inst;
                                      "src1" :: Data;
                                      "src2" :: Data }.
    Definition longLatRegister := MethodSig "longLatRegister"(Struct LongLatStr): Void.
    Definition longLatGetResult := MethodSig "longLatGetResult"(Void): Struct Exec.

    Definition longLat :=
      MODULE {
        Rule longLatStart :=
          Call inp1 <- regReadFirst();
          LET instVal <- #inp1!RegReadT@.inst;
          Assert (! (isNotLongLat _ instVal));
          Call longLatVal <- readLongLatCall();
          Assert !#longLatVal;
          Call writeLongLatCall($$ true);
          Retv

        with Rule longLatDrop :=
          Call epochsMatchVal <- epochsMatchCall();
          Assert !#epochsMatchVal;
          Call inp1 <- regReadPop();
          Call longLatVal <- readLongLatCall();
          Assert #longLatVal;
          Call writeLongLatCall($$ false);
          Retv

        with Rule "longLatFinish_init" :=
          Call epochsMatchVal <- epochsMatchCall();
          Assert #epochsMatchVal;
          Call inp1 <- regReadFirst();
          LET pcVal <- #inp1!RegReadT@.pc;
          LET instVal <- #inp1!RegReadT@.inst;
          LET src1Val <- #inp1!RegReadT@.src1;
          LET src2Val <- #inp1!RegReadT@.src2;
          Assert (! (isNotLongLat _ instVal));
          Call longLatVal <- readLongLatCall();
          Assert #longLatVal;
          Call writeLongLatCall($$ false);

          Call longLatRegister(STRUCT { "inst" ::= #instVal;
                                        "src1" ::= #src1Val;
                                        "src2" ::= #src2Val });
          Retv

        with Rule "longLatFinish_done" :=
          Call execVal <- longLatGetResult();
          Call inp1 <- regReadPop();
          Call execEnq(STRUCT { wbEpoch ::= #inp1!RegReadT@.wbEpoch;
                                pc ::= #inp1!RegReadT@.pc;
                                instVToPRp ::= #inp1!RegReadT@.instVToPRp;
                                inst ::= #inp1!RegReadT@.inst;
                                exec ::= #execVal
                              });
          Retv
      }.

    Definition longLatImpl := longLat. (* TODO: add handlers. *)
    
  End Impl.

End Processor.


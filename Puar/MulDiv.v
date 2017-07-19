Require Import Kami.
Require Import Lib.Indexer Lib.Struct Lib.FMap Lib.Reflection.
Require Import Kami.Tactics Kami.SemFacts.
Require Import Puar.Useful Puar.Processor FunctionalExtensionality.

(* Below implements a radix-4 Booth multiplier. *)
Section Multiplier64.
  (* NOTE: hard to declare [LogNumPhases] and [NumBitsPerPhase] as variables,
   * since truncation and extension require certain equation w.r.t. bit-lengths.
   *)
  (* Variable LogNumPhases NumBitsPerPhase: nat. *)
  Definition LogNumPhases := 3.
  Definition NumBitsPerPhase := 8.

  Local Definition NumPhases := wordToNat (wones LogNumPhases) + 1.
  Local Definition NumBits := NumPhases * NumBitsPerPhase.
  Local Definition MultBits := 2 * NumBits + 2.

  Definition BoothInStr := STRUCT { "multiplicand" :: Bit NumBits;
                                    "multiplier" :: Bit NumBits }.
  Definition BoothOutStr := STRUCT { "high" :: Bit NumBits;
                                     "low" :: Bit NumBits }.

  Definition boothRegister := MethodSig "boothRegister"(Struct BoothInStr): Void.
  Definition boothGetResult := MethodSig "boothGetResult"(Void): Struct BoothOutStr.

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

  Definition boothMultiplier :=
    MODULE {
      Register "m_pos" : Bit MultBits <- Default
      with Register "m_neg" : Bit MultBits <- Default
      with Register "p" : Bit MultBits <- Default
      with Register "cnt" : Bit (S LogNumPhases) <- Default

      with Method "boothRegister"(src: Struct BoothInStr): Void :=
        LET m : Bit (pred NumBits + 1) <- #src!BoothInStr@."multiplicand";
        LET m_msb <- UniBit (TruncLsb _ 1) #m;
        LET m_neg <- (UniBit (Inv _) #m) + $1;
        LET m_neg_msb <- UniBit (TruncLsb _ 1) #m_neg;
        
        Write "m_pos" : Bit MultBits <-
          BinBit (Concat _ (S NumBits)) (BinBit (Concat _ _) #m_msb #m) $0;
        Write "m_neg" : Bit MultBits <-
          BinBit (Concat _ (S NumBits)) (BinBit (Concat _ _) #m_neg_msb #m_neg) $0;
        
        LET r <- #src!BoothInStr@."multiplier";
        Write "p" : Bit MultBits <-
          BinBit (Concat (S NumBits) _) $0 (BinBit (Concat _ 1) #r $0);

        Write "cnt" : Bit (S LogNumPhases) <- $(NumPhases);
        Retv

      with Method "boothGetResult"(): Struct BoothOutStr :=
        Read cnt : Bit LogNumPhases <- "cnt";
        Assert (#cnt == $0);

        Read p : Bit MultBits <- "p";
        LET high : Bit NumBits <- UniBit (ConstExtract (S NumBits) NumBits 1) #p;
        LET low : Bit NumBits <- UniBit (ConstExtract 1 NumBits (S NumBits)) #p;

        LET ret : Struct BoothOutStr <- STRUCT { "high" ::= $$Default; "low" ::= #low };
        Ret #ret
            
      with Rule "boothStep" :=
        Read cnt : Bit LogNumPhases <- "cnt";
        Assert (#cnt != $0);

        Read m_pos : Bit MultBits <- "m_pos";
        Read m_neg : Bit MultBits <- "m_neg";
        Read p : Bit MultBits <- "p";

        boothSteps
          NumBitsPerPhase m_pos m_neg p
          (fun np => Write "p" <- #np; Retv)
    }.

  Definition boothMultiplierSpec :=
    MODULE {
      Register "p" : Bit (2 * NumBits) <- Default

      with Method "boothRegister"(src: Struct BoothInStr): Void :=
        LET m : Bit NumBits <- #src!BoothInStr@."multiplicand";
        LET m_ext : Bit (2 * NumBits) <- UniBit (SignExtendTrunc _ _) #m;
        LET r : Bit NumBits <- #src!BoothInStr@."multiplier";
        LET r_ext : Bit (2 * NumBits) <- UniBit (SignExtendTrunc _ _) #m;

        Write "p" <- #m_ext *s #r_ext;
        Retv

      with Method "boothGetResult"(): Struct BoothOutStr :=
        Read p : Bit (NumBits + NumBits) <- "p";
        LET high : Bit NumBits <- UniBit (TruncLsb _ _) #p;
        LET low : Bit NumBits <- UniBit (Trunc _ _) #p;

        LET ret : Struct BoothOutStr <- STRUCT { "high" ::= $$Default; "low" ::= #low };
        Ret #ret
    }.

End Multiplier64.

Section Divider.
End Divider.

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


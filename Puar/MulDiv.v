Require Import Kami.
Require Import Lib.Indexer Lib.Struct Lib.FMap Lib.Reflection.
Require Import Kami.Tactics Kami.SemFacts.
Require Import Puar.Useful Puar.Processor Puar.Multiplier Puar.Divider.
Require Import FunctionalExtensionality.

Section Processor.
  Variables VAddr PAddr Inst Mode MemException ExecException: Kind.

  Variable isNotLongLat: forall ty, ty Inst -> Bool @ ty.
  
  Variable isMul: forall ty, ty Inst -> Bool @ ty.
  Variable isDiv: forall ty, ty Inst -> Bool @ ty.
  Variable isRem: forall ty, ty Inst -> Bool @ ty.

  Definition MulSign := Bit 2.
  Definition MulSignSS : ConstT MulSign := WO~0~0.
  Definition MulSignSU : ConstT MulSign := WO~0~1.
  Definition MulSignUU : ConstT MulSign := WO~1~0.
  Variable getMulSign: forall ty, ty Inst -> MulSign @ ty.
  Variable getDivSign: forall ty, ty Inst -> Bool @ ty.

  Section Spec.
    Variable NumDataBytes: nat.

    Definition Data := Bit (8 * NumDataBytes).
    Local Notation Exec := (Exec NumDataBytes VAddr ExecException).

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
      - refine (IF (getMulSign _ inst == $$MulSignSS)
                then #val1 *s #val2
                else (IF (getMulSign _ inst == $$MulSignSU)
                      then #val1 *su #val2
                      else #val1 * #val2))%kami_expr.
      - refine (IF (getDivSign _ inst == $$ true)
                then #val1 /s #val2
                else #val1 / #val2)%kami_expr.
      - refine (IF (getDivSign _ inst == $$ true)
                then BinBit (Rem _ true) #val1 #val2
                else BinBit (Rem _ false) #val1 #val2)%kami_expr.
    Defined.

    Definition longLatSpec :=
      getModFromSin (@LongLatency
                       NumDataBytes VAddr PAddr Inst Mode MemException ExecException
                       isNotLongLat execFnLongLatSpec).

  End Spec.

  Section Impl64.
    Definition NumDataBytes := 8.
    Definition Data64 := Bit (8 * NumDataBytes).

    Local Notation Exec := (Exec NumDataBytes VAddr ExecException).
    Local Notation regReadFirst := (regReadFirst NumDataBytes VAddr PAddr Inst Mode MemException).
    Local Notation regReadPop := (regReadPop NumDataBytes VAddr PAddr Inst Mode MemException).
    Local Notation RegReadT := (RegReadT NumDataBytes VAddr PAddr Inst Mode MemException).
    Local Notation execEnq := (execEnq NumDataBytes VAddr PAddr Inst Mode
                                       MemException ExecException).

    Definition longLat :=
      MODULE {
        Register "llRegistered" : Bool <- false
        with Register "llHasResult" : Bool <- false
        with Register "llInst" : Inst <- Default
        with Register "llSrc1" : Data64 <- Default
        with Register "llSrc2" : Data64 <- Default
        with Register "llRes" : Data64 <- Default
                                        
        with Rule longLatStart :=
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

        with Rule "longLatWork" :=
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

          Read reg <- "llRegistered";
          Assert !#reg;
          Write "llRegistered" <- $$true;

          Write "llInst" <- #instVal;
          Write "llSrc1" <- #src1Val;
          Write "llSrc2" <- #src2Val;
          Retv

        with Rule "longLatMult" :=
          Read reg <- "llRegistered";
          Assert #reg;

          Read inst : Inst <- "llInst";
          Read src1 : Data64 <- "llSrc1";
          Read src2 : Data64 <- "llSrc2";

          Assert (isMul _ inst);

          If (getMulSign _ inst == $$MulSignSS)
          then
            Call boothMultRegister(
              STRUCT { "multiplicand" ::= UniBit (SignExtendTrunc _ _) #src1;
                       "multiplier" ::= UniBit (SignExtendTrunc _ _) #src2 });
            Retv
          else
            If (getMulSign _ inst == $$MulSignSU)
            then
              Call boothMultRegister(
                STRUCT { "multiplicand" ::= UniBit (SignExtendTrunc _ _) #src1;
                         "multiplier" ::= UniBit (ZeroExtendTrunc _ _) #src2 });
              Retv
            else
              Call boothMultRegister(
                STRUCT { "multiplicand" ::= UniBit (ZeroExtendTrunc _ _) #src1;
                         "multiplier" ::= UniBit (ZeroExtendTrunc _ _) #src2 });
              Retv;
            Retv;
          Retv

        with Rule "longLatDiv" :=
          Read reg <- "llRegistered";
          Assert #reg;

          Read inst : Inst <- "llInst";
          Read src1 : Data64 <- "llSrc1";
          Read src2 : Data64 <- "llSrc2";

          Assert (isDiv _ inst || isRem _ inst);

          If (getMulSign _ inst == $$MulSignSS)
          then
            Call nrDivRegister(
              STRUCT { "dividend" ::= UniBit (ZeroExtendTrunc _ 64) (UniBit (Trunc 63 1) #src1);
                       "divisor" ::= UniBit (ZeroExtendTrunc _ 64) (UniBit (Trunc 63 1) #src2) });
            Retv
          else
            If (getMulSign _ inst == $$MulSignSU)
            then
              Call nrDivRegister(
                STRUCT { "dividend" ::= UniBit (ZeroExtendTrunc _ 64) (UniBit (Trunc 63 1) #src1);
                         "divisor" ::= #src2 });
              Retv
            else
              Call nrDivRegister(STRUCT { "dividend" ::= #src1; "divisor" ::= #src2 });
              Retv;
            Retv;
          Retv

        with Rule "longLatMultFinish" :=
          Read inst : Inst <- "llInst";
          Assert (isMul _ inst);

          Call mres <- boothMultGetResult();
          (* TODO: write appropriate values to "llRes" *)

          Write "llHasResult" <- $$true;
          Retv

        with Rule "longLatDivFinish" :=
          Read inst : Inst <- "llInst";
          Assert (isDiv _ inst || isRem _ inst);

          Call dres <- nrDivGetResult();
          (* TODO: write appropriate values to "llRes" *)

          Write "llHasResult" <- $$true;
          Retv
            
        with Rule "longLatFinish_done" :=
          Read hasResult <- "llHasResult";
          Assert #hasResult;
          Read res <- "llRes";
          
          LET execVal <- STRUCT { "data" ::= #res;
                                  "memVAddr" ::= $$Default;
                                  "exception" ::= $$Default;
                                  "nextPc" ::= $$Default (* (pc + 4)? *) };
          Call inp1 <- regReadPop();
          Call execEnq(STRUCT { wbEpoch ::= #inp1!RegReadT@.wbEpoch;
                                pc ::= #inp1!RegReadT@.pc;
                                instVToPRp ::= #inp1!RegReadT@.instVToPRp;
                                inst ::= #inp1!RegReadT@.inst;
                                exec ::= #execVal
                              });

          Write "llRegistered" <- $$false;
          Write "llHasResult" <- $$false;
          Retv
      }.

    Definition longLatImpl :=
      (longLat ++ boothMultiplierImpl ++ nrDividerImpl)%kami.
    
  End Impl64.


  Theorem longLat_refines:
    longLatImpl <<== (longLatSpec NumDataBytes).
  Proof.
  Admitted.
  
End Processor.


Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import Fetch AbstractIsa.

Set Implicit Arguments.

Section Processor.
  Variables addrSize dataBytes rfIdx: nat.

  Section BHT.
    Variable (indexSize: nat).

    Definition satCntInit: ConstT (Vector (Bit 2) indexSize) :=
      ConstVector (replicate (ConstBit (natToWord _ 1)) indexSize).

    Definition getIndex {ty} (pcv: fullType ty (SyntaxKind (Bit addrSize))):
      Expr ty (SyntaxKind (Bit indexSize)) :=
      UniBit (ZeroExtendTrunc _ _) (#pcv >> $$(natToWord 2 2))%kami_expr.

    Definition getTaken {ty} (cntv: fullType ty (SyntaxKind (Bit 2))):
      Expr ty (SyntaxKind Bool) :=
      (IF (#cntv >> $$(natToWord 1 1) == $0)
       then $$(ConstBool false)
       else $$(ConstBool true))%kami_expr.

    Definition nextSatCnt {ty} (cntv: fullType ty (SyntaxKind (Bit 2)))
               (takenv: fullType ty (SyntaxKind Bool)):
      Expr ty (SyntaxKind (Bit 2)) :=
      (IF #takenv
       then (IF (#cntv == $0) then $1 else $3)
       else (IF (#cntv == $3) then $2 else $0)
      )%kami_expr.

    Definition bhtUpdateStr :=
      STRUCT { "pc" :: Bit addrSize; "taken" :: Bool }.

    Definition bhtPredTaken := MethodSig "predTaken"(Bit addrSize): Bool.
    Definition bhtUpdate := MethodSig "update"(Struct bhtUpdateStr): Void.

    Definition bht :=
      MODULE {
        Register "satCnt" : Vector (Bit 2) indexSize <- satCntInit

        with Method "predTaken"(pc: Bit addrSize): Bool :=
          LET index <- getIndex pc;
          Read satCnt <- "satCnt";
          LET cnt <- #satCnt@[#index];
          LET ret <- getTaken cnt;
          Ret #ret

        with Method "update"(upd: Struct bhtUpdateStr): Void :=
          LET pc <- #upd!bhtUpdateStr@."pc";
          LET taken <- #upd!bhtUpdateStr@."taken";
          LET index <- getIndex pc;
          Read satCnt <- "satCnt";
          LET cnt <- #satCnt@[#index];
          LET next <- nextSatCnt cnt taken;
          Write "satCnt" <- #satCnt@[#index <- #next];
          Retv
      }.

    Variable (bhtTrainName: string).

    Definition bhtTrainDeq := MethodSig (bhtTrainName -- "deq")(): Struct bhtUpdateStr.
    
    Definition bhtTrain :=
      MODULE {
        Rule "trainBht" :=
          Call tr <- bhtTrainDeq();
          Call bhtUpdate(#tr);
          Retv
      }.

  End BHT.

  Section Decode.
    Variables (f2dName d2rName iMemRepName: string).
    Variable decodeInst: DecodeT dataBytes rfIdx.

    Definition f2dDeq := MethodSig (f2dName -- "deq")(): Struct (F2D addrSize).
    Definition iMemRep := MethodSig iMemRepName(): Struct (RsToProc dataBytes).

    Definition D2R :=
      STRUCT { "pc" :: Bit addrSize;
               "predPc" :: Bit addrSize;
               "dInst" :: Struct (decodedInst dataBytes rfIdx);
               "exeEpoch" :: Bool }.
    Definition d2rEnq := MethodSig (d2rName -- "enq")(Struct D2R): Void.

    Definition decode :=
      MODULE {
        Rule "doDecode" :=
          Call f2d <- f2dDeq();
          LET pc <- #f2d!(F2D addrSize)@."pc";
          Call instStr <- iMemRep();
          LET inst <- #instStr!(RsToProc dataBytes)@."data";

          Call decEpoch <- (getEpoch "dec")();
          Call exeEpoch <- (getEpoch "exe")();

          If (#exeEpoch == #f2d!(F2D addrSize)@."exeEpoch"
              && #decEpoch == #f2d!(F2D addrSize)@."decEpoch")
          then
            LET predPc <- #f2d!(F2D addrSize)@."predPc";
            LET dInst <- decodeInst _ inst;
            If (#dInst!(decodedInst dataBytes rfIdx)@."iType" == $$iTypeBr)
            then
              Call taken <- bhtPredTaken(#pc);
              LET bhtPredPc : Bit addrSize <-
                (IF #taken
                 then #pc + UniBit (ZeroExtendTrunc _ _) #dInst!(decodedInst dataBytes rfIdx)@."imm"
                 else #pc + $4);
              If (#predPc != #bhtPredPc)
              then
                LET ret : Struct (Maybe (Bit addrSize)) <- STRUCT { "isValid" ::= $$true;
                                                                    "value" ::= #bhtPredPc };
                Ret #ret
              else
                LET ret : Struct (Maybe (Bit addrSize)) <- STRUCT { "isValid" ::= $$false;
                                                                    "value" ::= $$Default };
                Ret #ret
              as ret;
              Ret #ret
            else
              If (#dInst!(decodedInst dataBytes rfIdx)@."iType" == $$iTypeJ)
              then
                LET jumpAddr <- #pc + UniBit (ZeroExtendTrunc _ _)
                                             #dInst!(decodedInst dataBytes rfIdx)@."imm";
                If (#predPc != #jumpAddr)
                then
                  LET ret : Struct (Maybe (Bit addrSize)) <- STRUCT { "isValid" ::= $$true;
                                                                      "value" ::= #jumpAddr };
                  Ret #ret
                else
                  LET ret : Struct (Maybe (Bit addrSize)) <- STRUCT { "isValid" ::= $$false;
                                                                      "value" ::= $$Default };
                  Ret #ret
                as ret;
                Ret #ret
              else Ret (STRUCT { "isValid" ::= $$false; "value" ::= $$Default })
              as ret;
              Ret #ret
            as ret;

            If (#ret!(Maybe (Bit addrSize))@."isValid")
            then
              Call (redirSetValid addrSize "dec")(
                     STRUCT { "pc" ::= #pc;
                              "nextPc" ::= #ret!(Maybe (Bit addrSize))@."value" });
              Call d2rEnq(STRUCT { "pc" ::= #pc;
                                   "predPc" ::= #ret!(Maybe (Bit addrSize))@."value";
                                   "dInst" ::= #dInst;
                                   "exeEpoch" ::= #exeEpoch });
              Retv
            else
              Call d2rEnq(STRUCT { "pc" ::= #pc;
                                   "predPc" ::= #predPc;
                                   "dInst" ::= #dInst;
                                   "exeEpoch" ::= #exeEpoch });
              Retv
            as _;
            Retv
              
          else
            Retv
          as _;
          Retv
      }.
    
  End Decode.

End Processor.


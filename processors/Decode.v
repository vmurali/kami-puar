Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import Fetch IMem Proc.RegFile AbstractIsa.

(* NOTE: Let's add the exception mechanism after proving without it. *)
(* Require Import Exception. *)

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

    Definition DecodedInst := decodedInst dataBytes rfIdx.
    
    Definition bhtPredPcStr :=
      STRUCT { "pc" :: Bit addrSize;
               "predPc" :: Bit addrSize;
               "dInst" :: Struct DecodedInst
             }.
    
    Definition bhtFrontEnd :=
      MODULE {
        Method "bhtPredPc"(pp: Struct bhtPredPcStr): Struct (Maybe (Bit addrSize)) :=
          LET dInst <- #pp!bhtPredPcStr@."dInst";
          LET pc <- #pp!bhtPredPcStr@."pc";
          LET predPc <- #pp!bhtPredPcStr@."predPc";
          LET iType <- #dInst!DecodedInst@."iType";
            
          If (#iType == $$iTypeBr)
          then
            Call taken <- bhtPredTaken(#pc);
            LET bhtPredPc : Bit addrSize <- (IF #taken
                                             then #pc + UniBit (ZeroExtendTrunc _ _)
                                                               #dInst!DecodedInst@."imm"
                                             else #pc + $4);
            If (#predPc != #bhtPredPc)
            then
              LET ret : Struct (Maybe (Bit addrSize)) <- STRUCT { "isValid" ::= $$true;
                                                                  "value" ::= #bhtPredPc };
              Ret #ret
            else (* #predPc == #bhtPredPc *)
              LET ret : Struct (Maybe (Bit addrSize)) <- STRUCT { "isValid" ::= $$false;
                                                                  "value" ::= $$Default };
              Ret #ret
            as ret;
            Ret #ret
          else (* #iType != $$iTypeBr *)
            If (#iType == $$iTypeJ)
            then
              LET jumpAddr <- #pc + UniBit (ZeroExtendTrunc _ _) #dInst!DecodedInst@."imm";
              If (#predPc != #jumpAddr)
              then
                LET ret : Struct (Maybe (Bit addrSize)) <- STRUCT { "isValid" ::= $$true;
                                                                    "value" ::= #jumpAddr };
                Ret #ret
              else (* #predPc == #jumpAddr *)
                LET ret : Struct (Maybe (Bit addrSize)) <- STRUCT { "isValid" ::= $$false;
                                                                    "value" ::= $$Default };
                Ret #ret
              as ret;
              Ret #ret
            else (* #iType != $$iTypeJ *)
              Ret (STRUCT { "isValid" ::= $$false; "value" ::= $$Default })
            as ret;
            Ret #ret
          as ret;

          Ret #ret
        }.

    Definition bhtPredPc :=
      MethodSig "bhtPredPc"(Struct bhtPredPcStr): Struct (Maybe (Bit addrSize)).

  End BHT.

  Section Decode.
    Variables (i2dName d2rName: string).
    Variable decodeInst: DecodeT dataBytes rfIdx.

    Definition I2D := I2D addrSize dataBytes.

    Definition i2dDeq := MethodSig (i2dName -- "deq")(): Struct I2D.

    Definition D2R :=
      STRUCT { "pc" :: Bit addrSize;
               "predPc" :: Bit addrSize;
               "dInst" :: Struct DecodedInst;
               "exeEpoch" :: Bool }.
    Definition d2rEnq := MethodSig (d2rName -- "enq")(Struct D2R): Void.

    Definition bpRegister := bpRegister rfIdx.

    Definition decode :=
      MODULE {
        Rule "killDecode" :=
          Call i2d <- i2dDeq();
          LET f2d <- #i2d!I2D@."f2dOrig";
          LET pc <- #f2d!(F2D addrSize)@."pc";
          LET instStr <- #i2d!I2D@."iMemRep";
          LET inst <- #instStr!(RsToProc dataBytes)@."data";

          Call decEpoch <- decGetEpoch2();
          Call exeEpoch <- exeGetEpoch2();

          Assert !(#exeEpoch == #f2d!(F2D addrSize)@."exeEpoch"
                   && #decEpoch == #f2d!(F2D addrSize)@."decEpoch");
          Retv
          
        with Rule "doDecode" :=
          Call i2d <- i2dDeq();
          LET f2d <- #i2d!I2D@."f2dOrig";
          LET pc <- #f2d!(F2D addrSize)@."pc";
          LET instStr <- #i2d!I2D@."iMemRep";
          LET inst <- #instStr!(RsToProc dataBytes)@."data";

          Call decEpoch <- decGetEpoch2();
          Call exeEpoch <- exeGetEpoch2();

          Assert (#exeEpoch == #f2d!(F2D addrSize)@."exeEpoch"
                  && #decEpoch == #f2d!(F2D addrSize)@."decEpoch");

          LET predPc <- #f2d!(F2D addrSize)@."predPc";
          LET dInst <- decodeInst _ inst;
          LET iType <- #dInst!DecodedInst@."iType";

          (* TODO: throw an exception if the below assertion fails *)
          Assert (#iType != $$iTypeUnsupported);

          (* Value bypassing related, may have some other iType's that need registration *)
          Call bpRegister(STRUCT { "hasDst" ::= #dInst!DecodedInst@."hasDst";
                                   "dst" ::= #dInst!DecodedInst@."dst";
                                   "isLd" ::= #iType == $$iTypeLd });
                  
          (* Branch prediction related *)
          Call predPc <- bhtPredPc(STRUCT { "pc" ::= #pc;
                                            "predPc" ::= #f2d!(F2D addrSize)@."predPc";
                                            "dInst" ::= #dInst });
          Call d2rEnq(STRUCT { "pc" ::= #pc;
                               "predPc" ::= #predPc!(Maybe (Bit addrSize))@."value";
                               "dInst" ::= #dInst;
                               "exeEpoch" ::= #exeEpoch });

          If (#predPc!(Maybe (Bit addrSize))@."isValid")
          then
            Call (redirSetValid addrSize "dec")(
                   STRUCT { "pc" ::= #pc;
                            "nextPc" ::= #predPc!(Maybe (Bit addrSize))@."value" });
            Retv;
          Retv
      }.

    Definition decodeNondet :=
      MODULE {
        Rule "killDecode" :=
          Call i2d <- i2dDeq();
          LET f2d <- #i2d!I2D@."f2dOrig";
          LET pc <- #f2d!(F2D addrSize)@."pc";
          LET instStr <- #i2d!I2D@."iMemRep";
          LET inst <- #instStr!(RsToProc dataBytes)@."data";

          Call decEpoch <- decGetEpoch2();
          Call exeEpoch <- exeGetEpoch2();

          Assert !(#exeEpoch == #f2d!(F2D addrSize)@."exeEpoch"
                   && #decEpoch == #f2d!(F2D addrSize)@."decEpoch");
          Retv

        with Rule "doDecode" :=
          Call i2d <- i2dDeq();
          LET f2d <- #i2d!I2D@."f2dOrig";
          LET pc <- #f2d!(F2D addrSize)@."pc";
          LET instStr <- #i2d!I2D@."iMemRep";
          LET inst <- #instStr!(RsToProc dataBytes)@."data";

          Call decEpoch <- decGetEpoch2();
          Call exeEpoch <- exeGetEpoch2();

          Assert (#exeEpoch == #f2d!(F2D addrSize)@."exeEpoch"
                  && #decEpoch == #f2d!(F2D addrSize)@."decEpoch");

          LET predPc <- #f2d!(F2D addrSize)@."predPc";
          LET dInst <- decodeInst _ inst;
          LET iType <- #dInst!DecodedInst@."iType";
            
          Assert (#iType != $$iTypeUnsupported);

          (* Value bypassing related, may have some other iType's that need registration *)
          Call bpRegister(STRUCT { "hasDst" ::= #dInst!DecodedInst@."hasDst";
                                   "dst" ::= #dInst!DecodedInst@."dst";
                                   "isLd" ::= #iType == $$iTypeLd });

          Nondet predPcN : SyntaxKind (Bit addrSize);
          Nondet isValid : SyntaxKind Bool;

          Call d2rEnq(STRUCT { "pc" ::= #pc;
                               "predPc" ::= #predPcN;
                               "dInst" ::= #dInst;
                               "exeEpoch" ::= #exeEpoch });

          If #isValid then
            Call (redirSetValid addrSize "dec")(
                   STRUCT { "pc" ::= #pc;
                            "nextPc" ::= #predPcN });
            Retv;
          Retv
      }.
    
  End Decode.

End Processor.

Hint Unfold bht bhtTrain bhtFrontEnd decode decodeNondet : ModuleDefs.

Hint Unfold satCntInit getIndex getTaken nextSatCnt bhtUpdateStr
     bhtPredTaken bhtUpdate bhtTrainDeq bhtPredPcStr
     I2D i2dDeq DecodedInst D2R d2rEnq : MethDefs.

Section Wf.
  Variables addrSize indexSize dataBytes rfIdx: nat.
  Variable decodeInst: DecodeT dataBytes rfIdx.

  Lemma bht_ModEquiv:
    ModPhoasWf (bht addrSize indexSize).
  Proof. kequiv. Qed.

  Lemma bhtTrain_ModEquiv:
    forall bhtTrainName, ModPhoasWf (bhtTrain addrSize bhtTrainName).
  Proof. kequiv. Qed.

  Lemma bhtFrontEnd_ModEquiv:
    ModPhoasWf (bhtFrontEnd addrSize dataBytes rfIdx).
  Proof. kequiv. Qed.

  Lemma decode_ModEquiv:
    forall i2dName d2rName, ModPhoasWf (decode addrSize i2dName d2rName decodeInst).
  Proof. kequiv. Qed.

  Lemma decodeNondet_ModEquiv:
    forall i2dName d2rName, ModPhoasWf (decodeNondet addrSize i2dName d2rName decodeInst).
  Proof. kequiv. Qed.

  Lemma bht_ModRegsWf:
    ModRegsWf (bht addrSize indexSize).
  Proof. kvr. Qed.

  Lemma bhtTrain_ModRegsWf:
    forall bhtTrainName, ModRegsWf (bhtTrain addrSize bhtTrainName).
  Proof. kvr. Qed.

  Lemma bhtFrontEnd_ModRegsWf:
    ModRegsWf (bhtFrontEnd addrSize dataBytes rfIdx).
  Proof. kvr. Qed.

  Lemma decode_ModRegsWf:
    forall i2dName d2rName, ModRegsWf (decode addrSize i2dName d2rName decodeInst).
  Proof. kvr. Qed.

  Lemma decodeNondet_ModRegsWf:
    forall i2dName d2rName, ModRegsWf (decodeNondet addrSize i2dName d2rName decodeInst).
  Proof. kvr. Qed.

End Wf.

Hint Resolve bht_ModEquiv bhtTrain_ModEquiv bhtFrontEnd_ModEquiv
     decode_ModEquiv decodeNondet_ModEquiv.
Hint Resolve bht_ModRegsWf bhtTrain_ModRegsWf bhtFrontEnd_ModRegsWf
     decode_ModRegsWf decodeNondet_ModRegsWf.


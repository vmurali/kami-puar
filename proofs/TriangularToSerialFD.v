Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.MemTypes Ex.MemAtomic Ex.NativeFifo.

Require Import Proc.Fetch Proc.Decode Proc.InOrderSixStage Proc.AbstractIsa Proc.Exception.

Set Implicit Arguments.

Section TriangularFD.
  Variables addrSize dataBytes rfIdx: nat.
  Variable decodeInst: DecodeT dataBytes rfIdx.

  Definition fetch := fetch addrSize dataBytes.
  Definition f2d := f2d addrSize.
  Definition decode := decode addrSize decodeInst.

  Definition iMemReqFifo :=
    @nativeFifo iMemReqName (Struct (RqFromProc dataBytes addrSize)) Default.
  Definition iMemRepFifo :=
    @nativeFifo iMemRepName (Struct (RsToProc dataBytes)) Default.

  Definition mid := mid iMemReqName iMemRepName addrSize dataBytes.

  (** The original implementation *)
  Definition FD := (fetch ++ f2d ++ decode ++ iMemReqFifo ++ mid ++ iMemRepFifo)%kami.

End TriangularFD.

Section SerialFD.
  Variables addrSize dataBytes rfIdx: nat.
  Variable decodeInst: DecodeT dataBytes rfIdx.

  Definition f2trName := "f2tr".
  Definition tr2dName := "tr2d".

  Definition F2Tr :=
    STRUCT { "f2dOrig" :: Struct (F2D addrSize);
             "iMemReq" :: Struct (RqFromProc addrSize dataBytes) }.

  Definition Tr2D :=
    STRUCT { "f2dOrig" :: Struct (F2D addrSize);
             "iMemRep" :: Struct (RsToProc dataBytes) }.

  Section Fetch.

    Definition f2trEnq := MethodSig (f2trName -- "enq")(Struct F2Tr): Void.

    Definition btbPredPc := btbPredPc addrSize.
    Definition redirGet := redirGet addrSize.
    Definition redirectStr := redirectStr addrSize.
    Definition btbUpdate := btbUpdate addrSize.

    Definition fetchSerial :=
      MODULE {
        Register "pc" : Bit addrSize <- Default

        with Rule "doFetch" :=
          Read pc <- "pc";
          Call predPc <- btbPredPc(#pc);
          Write "pc" <- #predPc;
          Call decEpoch <- (getEpoch "dec")();
          Call exeEpoch <- (getEpoch "exe")();
          Call resetException();
          Call f2trEnq (
                 STRUCT { "f2dOrig" ::= STRUCT { "pc" ::= #pc;
                                                 "predPc" ::= #predPc;
                                                 "decEpoch" ::= #decEpoch;
                                                 "exeEpoch" ::= #exeEpoch };
                          "iMemReq" ::= STRUCT { "addr" ::= #pc;
                                                 "op" ::= $$false;
                                                 "data" ::= $$Default }
                        });
          Retv

        with Rule "redirect" :=
          Call exeRedir <- (redirGet "exe")();
          If (#exeRedir!(Maybe (Struct redirectStr))@."isValid")
          then
            LET r <- #exeRedir!(Maybe (Struct redirectStr))@."value";
            Write "pc" <- #r!redirectStr@."nextPc";
            Call btbUpdate(STRUCT { "curPc" ::= #r!redirectStr@."pc";
                                    "nextPc" ::= #r!redirectStr@."nextPc" });
            Call (toggleEpoch "exe")();
            Retv
          else
            Call decRedir <- (redirGet "dec")();
            If (#decRedir!(Maybe (Struct redirectStr))@."isValid")
            then
              LET r <- #decRedir!(Maybe (Struct redirectStr))@."value";
              Write "pc" <- #r!redirectStr@."nextPc";
              Call btbUpdate(STRUCT { "curPc" ::= #r!redirectStr@."pc";
                                      "nextPc" ::= #r!redirectStr@."nextPc" });
              Call (toggleEpoch "dec")();
              Retv;
            Retv;
          Call (redirSetInvalid "exe")();
          Call (redirSetInvalid "dec")();
          Retv
      }.

  End Fetch.

  Section FDTrans.
    Definition f2trDeq := MethodSig (f2trName -- "deq")(): Struct F2Tr.
    Definition tr2dEnq := MethodSig (tr2dName -- "enq")(Struct Tr2D): Void.
    Definition exec :=
      MethodSig "exec"(Struct (RqFromProc addrSize dataBytes)) : Struct (RsToProc dataBytes).

    Definition fdtrans :=
      MODULE {
        Rule "processLd" :=
          Call f2tr <- f2trDeq();
          LET f2dOrig <- #f2tr!F2Tr@."f2dOrig";
          LET req <- #f2tr!F2Tr@."iMemReq";
          Assert !#req!(RqFromProc addrSize dataBytes)@."op";
          Call rep <- exec(#req);
          Call tr2dEnq(STRUCT { "f2dOrig" ::= #f2dOrig;
                                "iMemRep" ::= #rep });
          Retv
            
        with Rule "processSt" :=
          Call f2tr <- f2trDeq();
          LET f2dOrig <- #f2tr!F2Tr@."f2dOrig";
          LET req <- #f2tr!F2Tr@."iMemReq";
          Assert #req!(RqFromProc addrSize dataBytes)@."op";
          Call rep <- exec(#req);
          Call tr2dEnq(STRUCT { "f2dOrig" ::= #f2dOrig;
                                "iMemRep" ::= #rep });
          Retv
      }.

  End FDTrans.

  Section Decode.
    Definition tr2dDeq := MethodSig (tr2dName -- "deq")(): Struct Tr2D.

    Definition DecodedInst := decodedInst dataBytes rfIdx.

    Definition D2R := D2R addrSize dataBytes rfIdx.
    Definition d2rEnq := d2rEnq addrSize dataBytes rfIdx d2rName.
    Definition bhtPredTaken := bhtPredTaken addrSize.

    Definition decodeSerial :=
      MODULE {
        Rule "doDecode" :=
          Call tr2d <- tr2dDeq();
          LET f2d <- #tr2d!Tr2D@."f2dOrig";
          LET pc <- #f2d!(F2D addrSize)@."pc";
          LET instStr <- #tr2d!Tr2D@."iMemRep";
          LET inst <- #instStr!(RsToProc dataBytes)@."data";

          Call decEpoch <- (getEpoch "dec")();
          Call exeEpoch <- (getEpoch "exe")();

          If (#exeEpoch == #f2d!(F2D addrSize)@."exeEpoch"
              && #decEpoch == #f2d!(F2D addrSize)@."decEpoch")
          then
            LET predPc <- #f2d!(F2D addrSize)@."predPc";
            LET dInst <- decodeInst _ inst;

            If (#dInst!DecodedInst@."iType" != $$iTypeUnsupported)
            then
              If (#dInst!DecodedInst@."iType" == $$iTypeBr)
              then
                Call taken <- bhtPredTaken(#pc);
                LET bhtPredPc : Bit addrSize <-
                  (IF #taken
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
              else (* #dInst!DecodedInst@."iType" != $$iTypeBr *)
                If (#dInst!DecodedInst@."iType" == $$iTypeJ)
                then
                  LET jumpAddr <- #pc + UniBit (ZeroExtendTrunc _ _)
                                               #dInst!DecodedInst@."imm";
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
                else (* #dInst!DecodedInst@."iType" != $$iTypeJ *)
                  Ret (STRUCT { "isValid" ::= $$false; "value" ::= $$Default })
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
              else (* ! #ret!(Maybe (Bit addrSize))@."isValid" *)
                Call d2rEnq(STRUCT { "pc" ::= #pc;
                                     "predPc" ::= #predPc;
                                     "dInst" ::= #dInst;
                                     "exeEpoch" ::= #exeEpoch });
                Retv;
              Retv
            else (* #dInst!DecodedInst@."iType" == $$iTypeUnsupported *)
              Call setException($$excIllegalInst);
              Retv;
            Retv;
          Retv
      }.

  End Decode.

  (** The serial implementation *)
  Definition FDSerial :=
    (fetchSerial ++ fdtrans ++ decodeSerial)%kami.

End SerialFD.

Section Correctness.
  Variables addrSize dataBytes rfIdx: nat.
  Variable decodeInst: DecodeT dataBytes rfIdx.

  Lemma fd_implements_fdSerial:
    (FD addrSize decodeInst) <<== (FDSerial addrSize decodeInst).
  Proof.
  Admitted.

End Correctness.


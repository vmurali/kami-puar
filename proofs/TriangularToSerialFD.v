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

  Section Fetch.
    Variables (iMemReqName f2dName: string).

    Definition F2D :=
      STRUCT { "f2dOrig" :: Struct (F2D addrSize);
               "iMemReq" :: Struct (RqFromProc addrSize dataBytes) }.
    Definition f2dEnq := MethodSig (f2dName -- "enq")(Struct F2D): Void.

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
          Call f2dEnq (
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

End SerialFD.



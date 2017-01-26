Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import Execute AbstractIsa.

Set Implicit Arguments.

Section Processor.
  Variables addrSize dataBytes rfIdx: nat.

  Section Mem.
    Variables (e2mName m2wName dMemReqName: string).
    
    Definition e2mDeq := MethodSig (e2mName -- "deq")(): Struct (E2M addrSize dataBytes rfIdx).

    Definition M2W := E2M addrSize dataBytes rfIdx.
    Definition m2wEnq := MethodSig (m2wName -- "enq")(Struct M2W): Void.

    Definition dMemReq := MethodSig dMemReqName(Struct (RqFromProc dataBytes (Bit addrSize))): Void.

    Definition mem :=
      MODULE {
        Rule "passMemory" :=
          Call e2m <- e2mDeq();
          Assert (#e2m!(E2M addrSize dataBytes rfIdx)@."poisoned");
          Call m2wEnq(#e2m);
          Retv

        with Rule "doMemory" :=
          Call e2m <- e2mDeq();
          Assert (!#e2m!(E2M addrSize dataBytes rfIdx)@."poisoned");

          LET eInst <- #e2m!(E2M addrSize dataBytes rfIdx)@."eInst";
          LET iType <- #eInst!(execInst addrSize dataBytes rfIdx)@."iType";

          If (#iType == $$iTypeLd)
          then
            Call dMemReq(STRUCT { "addr" ::= #eInst!(execInst addrSize dataBytes rfIdx)@."addr";
                                  "op" ::= $$false;
                                  "data" ::= $$Default });
            Retv
          else
            If (#iType == $$iTypeSt)
            then
              Call dMemReq(STRUCT { "addr" ::= #eInst!(execInst addrSize dataBytes rfIdx)@."addr";
                                    "op" ::= $$true;
                                    "data" ::= #eInst!(execInst addrSize dataBytes rfIdx)@."data" });
              Retv
            else
              Retv
            as _;
            Retv
          as _;

          Call m2wEnq(#e2m);
          Retv

      }.

  End Mem.
    
End Processor.


Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import AbstractIsa RegRead Mem Exception.

Set Implicit Arguments.

Section Processor.
  Variables addrSize dataBytes rfIdx: nat.

  Section Writeback.
    Variables (m2wName dMemRepName: string).
    
    Definition m2wDeq := MethodSig (m2wName -- "deq")(): Struct (M2W addrSize dataBytes rfIdx).
    Definition dMemRep := MethodSig dMemRepName(): Struct (RsToProc dataBytes).

    (* TODO: implement *)
    Definition csrf :=
      MODULE {
        Rule "dummy" := Retv
      }.

    (* TODO: exception handling *)
    
    Definition writeback :=
      MODULE {
        Rule "noWriteback" :=
          Call m2w <- m2wDeq();
          Call bpRemove();
          Assert (#m2w!(M2W addrSize dataBytes rfIdx)@."poisoned");
          Retv

        with Rule "doWriteback" :=
          Call m2w <- m2wDeq();
          Call bpRemove();
          Assert (!#m2w!(M2W addrSize dataBytes rfIdx)@."poisoned");

          LET eInst <- #m2w!(M2W addrSize dataBytes rfIdx)@."eInst";
                                                              
          Assert (#eInst!(execInst addrSize dataBytes rfIdx)@."hasDst");

          If (#eInst!(execInst addrSize dataBytes rfIdx)@."iType" == $$iTypeLd)
          then
            Call data <- dMemRep();
            Ret #data!(RsToProc dataBytes)@."data"
          else
            Ret (#eInst!(execInst addrSize dataBytes rfIdx)@."data")
          as data;
          
          Call (rfwr dataBytes rfIdx)(
                 STRUCT { "idx" ::= #eInst!(execInst addrSize dataBytes rfIdx)@."dst";
                          "value" ::= #data });
          Retv
      }.

  End Writeback.
          
End Processor.


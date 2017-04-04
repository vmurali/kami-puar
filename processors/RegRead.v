Require Import Kami.
Require Import Lib.CommonTactics Lib.Indexer.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import Decode Proc.RegFile AbstractIsa.

Set Implicit Arguments.

Section Processor.
  Variables addrSize dataBytes rfIdx csrIdx: nat.

  Section RegRead.
    Variables (d2rName r2eName: string).
    
    Definition d2rDeq :=
      MethodSig (d2rName -- "deq")(): Struct (D2R addrSize dataBytes rfIdx).

    Definition D2R := D2R addrSize dataBytes rfIdx.

    Definition R2E :=
      STRUCT { "pc" :: Bit addrSize;
               "predPc" :: Bit addrSize;
               "dInst" :: Struct (decodedInst dataBytes rfIdx);
               "rVal1" :: Data dataBytes;
               "rVal2" :: Data dataBytes;
               "exeEpoch" :: Bool }.
    Definition r2eEnq := MethodSig (r2eName -- "enq")(Struct R2E): Void.

    Definition rfrd1 := rfrd1 dataBytes rfIdx.
    Definition rfrd2 := rfrd2 dataBytes rfIdx.
    Definition bpSearch1 := bpSearch1 dataBytes rfIdx.
    Definition bpSearch2 := bpSearch2 dataBytes rfIdx.
  
    Definition regRead :=
      MODULE {
        Rule "doRegRead" :=
          Call d2r <- d2rDeq();
          LET dInst <- #d2r!D2R@."dInst";
          LET src1 <- #dInst!(decodedInst dataBytes rfIdx)@."src1";
          LET src2 <- #dInst!(decodedInst dataBytes rfIdx)@."src2";

          Call bpVal1 <- bpSearch1(#src1);
          Call bpVal2 <- bpSearch2(#src2);

          LET bst1 <- #bpVal1!(BypassStr dataBytes)@."state";
          LET bst2 <- #bpVal2!(BypassStr dataBytes)@."state";

          Assert (#bst1 != $$bypassStStallE && #bst1 != $$bypassStStallM);
          Assert (#bst2 != $$bypassStStallE && #bst2 != $$bypassStStallM);
                                                       
          If (#bst1 == $$bypassStClean)
          then 
            Call rVal1 <- rfrd1(#src1);
            Ret #rVal1
          else
            Ret #bpVal1!(BypassStr dataBytes)@."value"
          as rVal1;            

          If (#bst2 == $$bypassStClean)
          then 
            Call rVal2 <- rfrd2(#src2);
            Ret #rVal2
          else
            Ret #bpVal2!(BypassStr dataBytes)@."value"
          as rVal2;            

          LET dst <- #dInst!(decodedInst dataBytes rfIdx)@."dst";

          Call r2eEnq(STRUCT { "pc" ::= #d2r!D2R@."pc";
                               "predPc" ::= #d2r!D2R@."predPc";
                               "dInst" ::= #dInst;
                               "rVal1" ::= #rVal1;
                               "rVal2" ::= #rVal2;
                               "exeEpoch" ::= #d2r!D2R@."exeEpoch" });
          Retv
      }.

  End RegRead.
        
End Processor.


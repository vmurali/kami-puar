Require Import Kami.
Require Import Lib.CommonTactics Lib.Indexer.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import Decode AbstractIsa.

Set Implicit Arguments.

Section Processor.
  Variables addrSize dataBytes rfIdx csrIdx: nat.

  Section RegFile.
    Definition rfStr := STRUCT { "idx" :: Bit rfIdx; "value" :: Data dataBytes }.

    Definition regFile :=
      MODULE {
        Register "rf" : Vector (Data dataBytes) rfIdx <- Default

        with Method "rd1" (idx: Bit rfIdx) : Data dataBytes :=
          Read rf <- "rf";
          Ret #rf@[#idx]

        with Method "rd2" (idx: Bit rfIdx) : Data dataBytes :=
          Read rf <- "rf";
          Ret #rf@[#idx]

        with Method "wr" (v: Struct rfStr) : Void :=
          Read rf <- "rf";
          Write "rf" <- #rf@[#v!rfStr@."idx" <- #v!rfStr@."value"];
          Retv
      }.
      
    Definition rfrd1 := MethodSig "rd1"(Bit rfIdx) : Data dataBytes.
    Definition rfrd2 := MethodSig "rd2"(Bit rfIdx) : Data dataBytes.
    Definition rfwr := MethodSig "wr"(Struct rfStr) : Void.

  End RegFile.

  Section Bypass.

    Definition BypassSt := Bit 2.
    Definition bypassStClean := WO~0~0.
    Definition bypassStStall := WO~0~1.
    Definition bypassStBypass := WO~1~0.
    
    Definition BypassStr := STRUCT { "state" :: BypassSt; "value" :: Data dataBytes }.

    (* TODO: implement *)
    (* joonwonc NOTE: merging rf and bypass together? need to discuss with Andy *)
    Definition bypass :=
      MODULE {
        Method "bpSearch1"(idx: Bit rfIdx): Struct BypassStr := (cheat _)
        with Method "bpSearch2"(idx: Bit rfIdx): Struct BypassStr := (cheat _)
        with Method "bpRegister"(idx: Bit rfIdx): Void := (cheat _)
        with Method "bpInsert"(v: Struct rfStr): Void := (cheat _)
        with Method "bpRemove"(): Void := (cheat _)
      }.

    Definition bpSearch1 := MethodSig "bpSearch1"(Bit rfIdx) : Struct BypassStr.
    Definition bpSearch2 := MethodSig "bpSearch2"(Bit rfIdx) : Struct BypassStr.
    Definition bpRegister := MethodSig "bpRegister"(Bit rfIdx) : Void.
    Definition bpInsert := MethodSig "bpInsert"(Struct rfStr) : Void.
    Definition bpRemove := MethodSig "bpRemove"() : Void.

  End Bypass.

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
  
    Definition regRead :=
      MODULE {
        Rule "doRegRead" :=
          Call d2r <- d2rDeq();
          LET dInst <- #d2r!D2R@."dInst";
          LET src1 <- #dInst!(decodedInst dataBytes rfIdx)@."src1";
          LET src2 <- #dInst!(decodedInst dataBytes rfIdx)@."src2";

          Call sb1 <- bpSearch1(#src1);
          Call sb2 <- bpSearch2(#src2);
          Assert (#sb1!BypassStr@."state" != $$bypassStStall &&
                  #sb2!BypassStr@."state" != $$bypassStStall);

          If (#sb1!BypassStr@."state" != $$bypassStClean)
          then
            Call rVal1 <- rfrd1(#src1);
            Ret #rVal1
          else
            Ret (#sb1!BypassStr@."value")
          as rVal1;
          
          If (#sb2!BypassStr@."state" != $$bypassStClean)
          then
            Call rVal2 <- rfrd2(#src2);
            Ret #rVal2
          else
            Ret (#sb2!BypassStr@."value")
          as rVal2;

          LET dst <- #dInst!(decodedInst dataBytes rfIdx)@."dst";
          Call bpRegister(#dst);

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


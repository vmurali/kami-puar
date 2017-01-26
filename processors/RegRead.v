Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import Decode AbstractIsa.

Set Implicit Arguments.

Section Processor.
  Variables addrSize dataBytes rfIdx: nat.

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

  Section Scoreboard.

    (* TODO: implement *)
    (* joonwonc NOTE: merging rf and scoreboard together? need to discuss with Andy *)

    Definition sbSearch1 := MethodSig "sbSearch1"(Bit rfIdx) : Struct (Maybe (Data dataBytes)).
    Definition sbSearch2 := MethodSig "sbSearch2"(Bit rfIdx) : Struct (Maybe (Data dataBytes)).

    Definition sbInsert := MethodSig "sbInsert"(Bit rfIdx) : Void.
    Definition sbInsertVal := MethodSig "sbInsertVal"(Struct rfStr) : Void.
    Definition sbRemove := MethodSig "sbRemove"() : Void.

  End Scoreboard.

  Section RegRead.
    Variables (d2rName r2eName: string).
    
    Definition d2rDeq := MethodSig (d2rName -- "deq")(): Struct (D2R addrSize dataBytes rfIdx).

    Definition R2E :=
      STRUCT { "pc" :: Bit addrSize;
               "predPc" :: Bit addrSize;
               "dInst" :: Struct (decodedInst rfIdx dataBytes);
               "rVal1" :: Data dataBytes;
               "rVal2" :: Data dataBytes;
               (* "csrVal" :: Data dataBytes; *)
               "exeEpoch" :: Bool }.
    Definition r2eEnq := MethodSig (r2eName -- "enq")(Struct R2E): Void.
  
    Definition regRead :=
      MODULE {
        Rule "doRegRead" :=
          Call d2r <- d2rDeq();
          LET dInst <- #d2r!(D2R addrSize dataBytes rfIdx)@."dInst";
          LET src1 <- #dInst!(decodedInst rfIdx dataBytes)@."src1";
          LET src2 <- #dInst!(decodedInst rfIdx dataBytes)@."src2";
          Call rVal1 <- rfrd1(#src1);
          Call rVal2 <- rfrd2(#src2);

          Call sb1 <- sbSearch1(#src1);
          Call sb2 <- sbSearch2(#src2);
          Assert (!#sb1!(Maybe (Data dataBytes))@."isValid" &&
                  !#sb2!(Maybe (Data dataBytes))@."isValid");

          LET dst <- #dInst!(decodedInst rfIdx dataBytes)@."dst";
          Call sbInsert(#dst);

          Call r2eEnq(STRUCT { "pc" ::= #d2r!(D2R addrSize dataBytes rfIdx)@."pc";
                               "predPc" ::= #d2r!(D2R addrSize dataBytes rfIdx)@."predPc";
                               "dInst" ::= #dInst;
                               "rVal1" ::= #rVal1;
                               "rVal2" ::= #rVal2;
                               "exeEpoch" ::= #d2r!(D2R addrSize dataBytes rfIdx)@."exeEpoch" });
          Retv
      }.

  End RegRead.
        
End Processor.


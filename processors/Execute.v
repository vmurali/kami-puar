Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import Fetch Decode RegRead Proc.RegFile AbstractIsa.

(* NOTE: Let's add the exception mechanism after proving without it. *)
(* Require Import Exception. *)

Set Implicit Arguments.

Section Processor.
  Variables addrSize dataBytes rfIdx: nat.
             
  Section Execute.
    Variables (r2eName e2mName bhtTrainName: string).
    Variable exec: ExecT addrSize dataBytes rfIdx.
    
    Definition r2eDeq := MethodSig (r2eName -- "enq")(): Struct (R2E addrSize dataBytes rfIdx).

    Definition E2M :=
      STRUCT { "eInst" :: Struct (execInst addrSize dataBytes rfIdx);
               "poisoned" :: Bool }.
    Definition e2mEnq := MethodSig (e2mName -- "enq")(Struct E2M): Void.

    Definition bhtTrainEnq :=
      MethodSig (bhtTrainName -- "enq")(Struct (bhtUpdateStr addrSize)): Void.

    Definition execInst := execInst addrSize dataBytes rfIdx.
    Definition bpInsertE := bpInsertE dataBytes rfIdx.

    Definition execute :=
      MODULE {
        Rule "killExecute" :=
          Call r2e <- r2eDeq();
          Call exeEpoch <- (getEpoch "exe")();

          Assert (#r2e!(R2E addrSize dataBytes rfIdx)@."exeEpoch" != #exeEpoch);

          Call e2mEnq(STRUCT { "eInst" ::= $$Default; "poisoned" ::= $$true });
          Retv

        with Rule "doExecute" :=
          Call r2e <- r2eDeq();
          Call exeEpoch <- (getEpoch "exe")();

          Assert (#r2e!(R2E addrSize dataBytes rfIdx)@."exeEpoch" == #exeEpoch);

          LET dInst <- #r2e!(R2E addrSize dataBytes rfIdx)@."dInst";
          LET iType <- #dInst!(decodedInst dataBytes rfIdx)@."iType";
          LET rVal1 <- #r2e!(R2E addrSize dataBytes rfIdx)@."rVal1";
          LET rVal2 <- #r2e!(R2E addrSize dataBytes rfIdx)@."rVal2";
          LET pc <- #r2e!(R2E addrSize dataBytes rfIdx)@."pc";
          LET predPc <- #r2e!(R2E addrSize dataBytes rfIdx)@."predPc";

          LET eInst <- exec _ dInst rVal1 rVal2 pc predPc;

          (* Value bypassing related *)
          If (#eInst!execInst@."hasDst")
          then
            Call bpInsertE(STRUCT { "idx" ::= #eInst!execInst@."dst";
                                    "value" ::= #eInst!execInst@."data" });
            Retv;
              
          (* To redirect a mispredicted pc *)
          If (#eInst!execInst@."mispredict")
          then
            Call (redirSetValid addrSize "exe")(
                   STRUCT { "pc" ::= #pc;
                            "nextPc" ::= #eInst!execInst@."addr" });
            Call bhtTrainEnq(
                   STRUCT { "pc" ::= #pc;
                            "taken" ::= #eInst!execInst@."brTaken" });
            Retv;

          Call e2mEnq(STRUCT { "eInst" ::= #eInst; "poisoned" ::= $$false });
          Retv
      }.

  End Execute.

End Processor.


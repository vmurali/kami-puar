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
    
    Definition r2eDeq := MethodSig (r2eName -- "deq")(): Struct (R2E addrSize dataBytes rfIdx).

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
          Call exeEpoch <- exeGetEpoch2();

          Assert (#r2e!(R2E addrSize dataBytes rfIdx)@."exeEpoch" != #exeEpoch);

          Call e2mEnq(STRUCT { "eInst" ::= $$Default; "poisoned" ::= $$true });
          Retv

        with Rule "doExecute" :=
          Call r2e <- r2eDeq();
          Call exeEpoch <- exeGetEpoch2();

          Assert (#r2e!(R2E addrSize dataBytes rfIdx)@."exeEpoch" == #exeEpoch);

          LET dInst <- #r2e!(R2E addrSize dataBytes rfIdx)@."dInst";
          LET iType <- #dInst!(decodedInst dataBytes rfIdx)@."iType";
          LET rVal1 <- #r2e!(R2E addrSize dataBytes rfIdx)@."rVal1";
          LET rVal2 <- #r2e!(R2E addrSize dataBytes rfIdx)@."rVal2";
          LET pc <- #r2e!(R2E addrSize dataBytes rfIdx)@."pc";
          LET predPc <- #r2e!(R2E addrSize dataBytes rfIdx)@."predPc";

          LET eInst <- exec _ dInst rVal1 rVal2 pc predPc;

          (* Value bypassing related *)
          Call bpInsertE(STRUCT { "hasDst" ::= #eInst!execInst@."hasDst";
                                  "dst" ::= #eInst!execInst@."dst";
                                  "value" ::= #eInst!execInst@."data" });
              
          (* To redirect a mispredicted pc *)
          If (#eInst!execInst@."mispredict")
          then
            Call (redirSetValid addrSize "exe")(
                   STRUCT { "pc" ::= #pc;
                            "nextPc" ::= #eInst!execInst@."addr" });
            Call bhtTrainEnq(
                   STRUCT { "pc" ::= #pc;
                            "taken" ::= #eInst!execInst@."brTaken" });
            Call exeToggleEpoch();
            Retv
          else
            Assert (#eInst!execInst@."addr" == #predPc);
            Retv;
            
          Call e2mEnq(STRUCT { "eInst" ::= #eInst; "poisoned" ::= $$false });
          Retv
      }.

    Definition executeNondet :=
      MODULE {
        Rule "killExecute" :=
          Call r2e <- r2eDeq();
          Call exeEpoch <- exeGetEpoch2();

          Assert (#r2e!(R2E addrSize dataBytes rfIdx)@."exeEpoch" != #exeEpoch);

          Call e2mEnq(STRUCT { "eInst" ::= $$Default; "poisoned" ::= $$true });
          Retv

        with Rule "doExecute" :=
          Call r2e <- r2eDeq();
          Call exeEpoch <- exeGetEpoch2();

          Assert (#r2e!(R2E addrSize dataBytes rfIdx)@."exeEpoch" == #exeEpoch);

          LET dInst <- #r2e!(R2E addrSize dataBytes rfIdx)@."dInst";
          LET iType <- #dInst!(decodedInst dataBytes rfIdx)@."iType";
          LET rVal1 <- #r2e!(R2E addrSize dataBytes rfIdx)@."rVal1";
          LET rVal2 <- #r2e!(R2E addrSize dataBytes rfIdx)@."rVal2";
          LET pc <- #r2e!(R2E addrSize dataBytes rfIdx)@."pc";
          LET predPc <- #r2e!(R2E addrSize dataBytes rfIdx)@."predPc";

          LET eInst <- exec _ dInst rVal1 rVal2 pc predPc;

          (* Value bypassing related *)
          Call bpInsertE(STRUCT { "hasDst" ::= #eInst!execInst@."hasDst";
                                  "dst" ::= #eInst!execInst@."dst";
                                  "value" ::= #eInst!execInst@."data" });
              
          (* To redirect a mispredicted pc *)
          If (#eInst!execInst@."mispredict")
          then
            Call (redirSetValid addrSize "exe")(
                   STRUCT { "pc" ::= #pc;
                            "nextPc" ::= #eInst!execInst@."addr" });
            Call exeToggleEpoch();
            Retv
          else
            Assert (#eInst!execInst@."addr" == #predPc);
            Retv;

          Call e2mEnq(STRUCT { "eInst" ::= #eInst; "poisoned" ::= $$false });
          Retv
      }.

    Definition executeNondetNR :=
      MODULE {
        Register "archPc" : Bit addrSize <- Default
          
        with Rule "killExecute" :=
          Call r2e <- r2eDeq();

          (** NOTE: should not have below assertion;
           * killing an instruction should be nondeterministic,
           * since sometimes instructions are killed in epoch mechanism,
           * even if they are generated by valid pc.
           *)
          (* Read pc <- "archPc"; *)
          (* Assert (#r2e!(R2E addrSize dataBytes rfIdx)@."pc" != #pc); *)

          Call e2mEnq(STRUCT { "eInst" ::= $$Default; "poisoned" ::= $$true });
          Retv

        with Rule "doExecute" :=
          Call r2e <- r2eDeq();
          Read pc <- "archPc";

          Assert (#r2e!(R2E addrSize dataBytes rfIdx)@."pc" == #pc);

          LET dInst <- #r2e!(R2E addrSize dataBytes rfIdx)@."dInst";
          LET iType <- #dInst!(decodedInst dataBytes rfIdx)@."iType";
          LET rVal1 <- #r2e!(R2E addrSize dataBytes rfIdx)@."rVal1";
          LET rVal2 <- #r2e!(R2E addrSize dataBytes rfIdx)@."rVal2";
          LET pc <- #r2e!(R2E addrSize dataBytes rfIdx)@."pc";
          LET predPc <- #r2e!(R2E addrSize dataBytes rfIdx)@."predPc";

          LET eInst <- exec _ dInst rVal1 rVal2 pc predPc;

          (* Value bypassing related *)
          Call bpInsertE(STRUCT { "hasDst" ::= #eInst!execInst@."hasDst";
                                  "dst" ::= #eInst!execInst@."dst";
                                  "value" ::= #eInst!execInst@."data" });
              
          (* To update pc, which is the right one, but no redirection! *)
          Write "archPc" <- #eInst!execInst@."addr";

          Call e2mEnq(STRUCT { "eInst" ::= #eInst; "poisoned" ::= $$false });
          Retv
      }.
    
  End Execute.

End Processor.

Hint Unfold execute executeNondet executeNondetNR : ModuleDefs.
Hint Unfold r2eDeq E2M e2mEnq bhtTrainEnq execInst bpInsertE : MethDefs.

Section Wf.
  Variables addrSize dataBytes rfIdx: nat.
  Variable exec: ExecT addrSize dataBytes rfIdx.
    
  Lemma execute_ModEquiv:
    forall r2eName e2mName bhtTrainName,
      ModPhoasWf (execute r2eName e2mName bhtTrainName exec).
  Proof. kequiv. Qed.

  Lemma executeNondet_ModEquiv:
    forall r2eName e2mName,
      ModPhoasWf (executeNondet r2eName e2mName exec).
  Proof. kequiv. Qed.

  Lemma executeNondetNR_ModEquiv:
    forall r2eName e2mName,
      ModPhoasWf (executeNondetNR r2eName e2mName exec).
  Proof. kequiv. Qed.

  Lemma execute_ModRegsWf:
    forall r2eName e2mName bhtTrainName,
      ModRegsWf (execute r2eName e2mName bhtTrainName exec).
  Proof. kvr. Qed.

  Lemma executeNondet_ModRegsWf:
    forall r2eName e2mName,
      ModRegsWf (executeNondet r2eName e2mName exec).
  Proof. kvr. Qed.

  Lemma executeNondetNR_ModRegsWf:
    forall r2eName e2mName,
      ModRegsWf (executeNondetNR r2eName e2mName exec).
  Proof. kvr. Qed.
  
End Wf.

Hint Resolve execute_ModEquiv executeNondet_ModEquiv executeNondetNR_ModEquiv.
Hint Resolve execute_ModRegsWf executeNondet_ModRegsWf executeNondetNR_ModRegsWf.


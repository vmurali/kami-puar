Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import AbstractIsa RegRead Mem DMem Proc.RegFile.

(* NOTE: Let's add the exception mechanism after proving without it. *)
(* Require Import Exception. *)

Set Implicit Arguments.

Section Processor.
  Variables addrSize dataBytes rfIdx: nat.

  Section Csr.
    Variable csrfIdx: nat.

    Definition csrfStr := STRUCT { "idx" :: Bit csrfIdx; "value" :: Data dataBytes }.

    Definition csrfRd := MethodSig "csrfRd"(Bit csrfIdx) : Data dataBytes.
    Definition csrfWr := MethodSig "csrfWr"(Struct csrfStr) : Void.

    Definition csrf :=
      MODULE {
        Register "csrf" : Vector (Data dataBytes) csrfIdx <- Default

        with Method "csrfRd" (idx: Bit csrfIdx) : Data dataBytes :=
          Read csrf <- "csrf";
          Ret #csrf@[#idx]

        with Method "csrfWr" (v: Struct csrfStr) : Void :=
          Read csrf <- "csrf";
          Write "csrf" <- #csrf@[#v!csrfStr@."idx" <- #v!csrfStr@."value"];
          Retv
      }.

  End Csr.

  Section Writeback.
    Variable d2wName: string.
    
    Definition d2wDeq := MethodSig (d2wName -- "deq")(): Struct (D2W addrSize dataBytes rfIdx).

    (* NOTE: handle exceptions later. *)
    (* NOTE: handle CSRs later. *)

    Definition bpRemove := bpRemove rfIdx.
    
    Definition writeback :=
      MODULE {
        Rule "noWriteback" :=
          Call d2w <- d2wDeq();
          LET m2wOrig <- #d2w!(D2W addrSize dataBytes rfIdx)@."m2wOrig";
          Assert (#m2wOrig!(M2W addrSize dataBytes rfIdx)@."poisoned");
          Retv

        with Rule "doWriteback" :=
          Call d2w <- d2wDeq();
          LET m2w <- #d2w!(D2W addrSize dataBytes rfIdx)@."m2wOrig";
          Assert (!#m2w!(M2W addrSize dataBytes rfIdx)@."poisoned");

          LET eInst <- #m2w!(M2W addrSize dataBytes rfIdx)@."eInst";
                                                              
          Assert (#eInst!(execInst addrSize dataBytes rfIdx)@."hasDst");

          If (#eInst!(execInst addrSize dataBytes rfIdx)@."iType" == $$iTypeLd)
          then
            LET data <- #d2w!(D2W addrSize dataBytes rfIdx)@."dMemRep";
            Ret #data!(RsToProc dataBytes)@."data"
          else
            Ret (#eInst!(execInst addrSize dataBytes rfIdx)@."data")
          as data;

          LET idx <- #eInst!(execInst addrSize dataBytes rfIdx)@."dst";
          Call (rfwr dataBytes rfIdx)(
                 STRUCT { "idx" ::= #idx;
                          "value" ::= #data });
          Call bpRemove(#idx);
          Retv
      }.

  End Writeback.
          
End Processor.

Hint Unfold csrfStr csrfRd csrfWr d2wDeq : MethDefs.
Hint Unfold csrf writeback : ModuleDefs.

Section Wf.
  Variables addrSize dataBytes rfIdx: nat.

  Lemma writeback_ModEquiv:
    forall d2wName,
      ModPhoasWf (writeback addrSize dataBytes rfIdx d2wName).
  Proof. kequiv. Qed.

  Lemma writeback_ModRegsWf:
    forall d2wName,
      ModRegsWf (writeback addrSize dataBytes rfIdx d2wName).
  Proof. kvr. Qed.

End Wf.

Hint Resolve writeback_ModEquiv.
Hint Resolve writeback_ModRegsWf.
     
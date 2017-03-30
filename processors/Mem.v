Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import Execute AbstractIsa.

Set Implicit Arguments.

Section Processor.
  Variables addrSize dataBytes rfIdx: nat.

  Section Mem.
    Variables (e2mName m2dName: string).
    
    Definition e2mDeq := MethodSig (e2mName -- "deq")(): Struct (E2M addrSize dataBytes rfIdx).

    Definition M2W := E2M addrSize dataBytes rfIdx.

    Definition M2D :=
      STRUCT { "m2wOrig" :: Struct M2W;
               "dMemReq" :: Struct (RqFromProc dataBytes (Bit addrSize)) }.
    
    Definition m2dEnq := MethodSig (m2dName -- "enq")(Struct M2D): Void.

    Definition mem :=
      MODULE {
        (* Rule "passMemory" := *)
        (*   Call e2m <- e2mDeq(); *)
        (*   Assert (#e2m!(E2M addrSize dataBytes rfIdx)@."poisoned"); *)
        (*   Call m2wEnq(#e2m); *)
        (*   Retv *)

        Rule "doMemory" :=
          Call e2m <- e2mDeq();
          Assert (!#e2m!(E2M addrSize dataBytes rfIdx)@."poisoned");

          LET eInst <- #e2m!(E2M addrSize dataBytes rfIdx)@."eInst";
          LET iType <- #eInst!(execInst addrSize dataBytes rfIdx)@."iType";

          If (#iType == $$iTypeLd)
          then
            Call m2dEnq (
              STRUCT { "m2wOrig" ::= #e2m;
                       "dMemReq" ::=
                          STRUCT { "addr" ::= #eInst!(execInst addrSize dataBytes rfIdx)@."addr";
                                   "op" ::= $$false;
                                   "data" ::= $$Default } });
            Retv
          else
            If (#iType == $$iTypeSt)
            then
              Call m2dEnq (
                STRUCT { "m2wOrig" ::= #e2m;
                         "dMemReq" ::=
                            STRUCT { "addr" ::= #eInst!(execInst addrSize dataBytes rfIdx)@."addr";
                                     "op" ::= $$true;
                                     "data" ::= #eInst!(execInst addrSize dataBytes rfIdx)@."data"
                                   } });
              Retv;
            Retv;
          Retv

      }.

  End Mem.
    
End Processor.

Hint Unfold mem : ModuleDefs.
Hint Unfold e2mDeq M2W M2D m2dEnq : MethDefs.

Section Wf.
  Variables addrSize dataBytes rfIdx: nat.

  Lemma mem_ModEquiv:
    forall e2mName m2dName, ModPhoasWf (mem addrSize dataBytes rfIdx e2mName m2dName).
  Proof. kequiv. Qed.

End Wf.

Hint Resolve mem_ModEquiv.
                                            

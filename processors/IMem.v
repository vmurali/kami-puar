Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import Fetch AbstractIsa.

Set Implicit Arguments.

Section IMem.
  Variables addrSize dataBytes rfIdx: nat.
  Variables (f2iName i2dName iExecName: string).

  Definition F2I := F2I addrSize dataBytes.

  Definition I2D :=
    STRUCT { "f2dOrig" :: Struct (F2D addrSize);
             "iMemRep" :: Struct (RsToProc dataBytes) }.

  Definition f2iDeq := MethodSig (f2iName -- "deq")(): Struct F2I.
  Definition i2dEnq := MethodSig (i2dName -- "enq")(Struct I2D): Void.

  Definition exec :=
    MethodSig iExecName(Struct (RqFromProc dataBytes (Bit addrSize))) : Struct (RsToProc dataBytes).

  Definition iMem :=
    MODULE {
      Rule "doIMem" :=
        Call f2i <- f2iDeq();
        LET f2dOrig <- #f2i!F2I@."f2dOrig";
        LET req <- #f2i!F2I@."iMemReq";
        Call rep <- exec(#req);
        Call i2dEnq(STRUCT { "f2dOrig" ::= #f2dOrig;
                             "iMemRep" ::= #rep });
        Retv
    }.

End IMem.

Hint Unfold iMem : ModuleDefs.
Hint Unfold F2I I2D f2iDeq i2dEnq exec : MethDefs.

Section Wf.
  Variables addrSize dataBytes rfIdx: nat.

  Lemma iMem_ModEquiv:
    forall f2iName i2dName iExecName,
      ModPhoasWf (iMem addrSize dataBytes f2iName i2dName iExecName).
  Proof. kequiv. Qed.

  Lemma iMem_ModRegsWf:
    forall f2iName i2dName iExecName,
      ModRegsWf (iMem addrSize dataBytes f2iName i2dName iExecName).
  Proof. kvr. Qed.

End Wf.

Hint Resolve iMem_ModEquiv.
Hint Resolve iMem_ModRegsWf.


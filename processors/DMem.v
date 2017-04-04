Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import Mem AbstractIsa.

Set Implicit Arguments.

Section DMem.
  Variables addrSize dataBytes rfIdx: nat.
  Variables (m2dName d2wName dExecName: string).

  Definition M2D := M2D addrSize dataBytes rfIdx.

  Definition D2W :=
    STRUCT { "m2wOrig" :: Struct (M2W addrSize dataBytes rfIdx);
             "dMemRep" :: Struct (RsToProc dataBytes) }.

  Definition m2dDeq := MethodSig (m2dName -- "deq")(): Struct M2D.
  Definition d2wEnq := MethodSig (d2wName -- "enq")(Struct D2W): Void.

  Definition exec :=
    MethodSig dExecName(Struct (RqFromProc dataBytes (Bit addrSize))) : Struct (RsToProc dataBytes).

  Definition M2W := M2W addrSize dataBytes rfIdx.
  Definition execInst := execInst addrSize dataBytes rfIdx.

  Definition dMem :=
    MODULE {
      Rule "passDMem" :=
        Call m2d <- m2dDeq();
        LET m2wOrig <- #m2d!M2D@."m2wOrig";
        Assert (#m2wOrig!M2W@."poisoned");
        Call d2wEnq(STRUCT { "m2wOrig" ::= #m2wOrig;
                             "dMemRep" ::= $$Default });
        Retv
     
      with Rule "doDMem" :=
        Call m2d <- m2dDeq();
        LET m2wOrig <- #m2d!M2D@."m2wOrig";
        Assert (!#m2wOrig!M2W@."poisoned");

        LET eInst <- #m2wOrig!M2W@."eInst";
        LET iType <- #eInst!execInst@."iType";

        If (#iType == $$iTypeLd || #iType == $$iTypeSt)
        then
          LET req <- #m2d!M2D@."dMemReq";
          Call rep <- exec(#req);
          Call d2wEnq (STRUCT { "m2wOrig" ::= #m2wOrig;
                                "dMemRep" ::= #rep });
          Retv
        else
          Call d2wEnq(STRUCT { "m2wOrig" ::= #m2wOrig;
                               "dMemRep" ::= $$Default });
          Retv;
        Retv
      }.

End DMem.

Hint Unfold dMem : ModuleDefs.
Hint Unfold M2D D2W m2dDeq d2wEnq exec : MethDefs.

Section Wf.
  Variables addrSize dataBytes rfIdx: nat.

  Lemma dMem_ModEquiv:
    forall m2dName d2wName dExecName,
      ModPhoasWf (dMem addrSize dataBytes rfIdx m2dName d2wName dExecName).
  Proof. kequiv. Qed.

End Wf.

Hint Resolve dMem_ModEquiv.
                                            

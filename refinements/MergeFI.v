Require Import Kami.
Require Import Lib.CommonTactics Lib.Indexer.
Require Import Kami.Decomposition Kami.ModuleBoundEx.
Require Import Ex.MemTypes Ex.OneEltFifo.

Require Import Proc.AbstractIsa Proc.Fetch Proc.IMem Proc.InOrderEightStage.
Require Import DropBranchPredictors.

Set Implicit Arguments.
Open Scope string.

Section Processor.
  Variables addrSize dataBytes rfIdx: nat.

  Variable decodeInst: DecodeT dataBytes rfIdx.
  Variable execInst: ExecT addrSize dataBytes rfIdx.

  Variables btbIndexSize btbTagSize bhtIndexSize bhtTrainSize: nat.
  Variables (getIndex: forall {ty}, fullType ty (SyntaxKind (Bit addrSize)) ->
                                    Expr ty (SyntaxKind (Bit btbIndexSize)))
            (getTag: forall {ty}, fullType ty (SyntaxKind (Bit addrSize)) ->
                                  Expr ty (SyntaxKind (Bit btbTagSize))).

  (** Fetch related *)
  Definition fetchNondet := fetchNondet addrSize dataBytes.
  Definition decRedir := decRedir addrSize.
  Definition exeRedir := exeRedir addrSize.
  Definition f2i := f2i addrSize dataBytes.

  (** IMem related *)
  Definition iMem := iMem addrSize dataBytes.
  Definition i2d := i2d addrSize dataBytes.

  (** Decode related *)
  Definition decodeNondet := decodeNondet addrSize decodeInst.
  Definition d2r := d2r addrSize dataBytes rfIdx.

  (** RegRead related *)
  Definition regRead := regRead addrSize dataBytes rfIdx.
  Definition rf := rf dataBytes rfIdx.
  Definition bypass := bypass dataBytes rfIdx.
  Definition r2e := r2e addrSize dataBytes rfIdx.

  (** Execute related *)
  Definition executeNondet := executeNondet execInst.
  Definition e2m := e2m addrSize dataBytes rfIdx.

  (** Mem related *)
  Definition mem := mem addrSize dataBytes rfIdx.
  Definition m2d := m2d addrSize dataBytes rfIdx.

  (** DMem related *)
  Definition dMem := dMem addrSize dataBytes rfIdx.
  Definition d2w := d2w addrSize dataBytes rfIdx.

  (** Writeback related *)
  Definition writeback := writeback addrSize dataBytes rfIdx.

  Definition inOrderEight1 := inOrderEight1 decodeInst execInst.

  Definition inOrderEight2 :=
    ((fetchNondet ++ f2i ++ iMem)
       ++ (decRedir ++ exeRedir ++ decEpoch ++ exeEpoch ++
                    i2d ++ decodeNondet ++ d2r ++
                    regRead ++ rf ++ bypass ++ r2e ++
                    executeNondet ++ e2m ++
                    mem ++ m2d ++
                    dMem ++ d2w ++
                    writeback))%kami.

  Section Refinement2.

    Theorem inOrderEight1_inOrderEight2: inOrderEight1 <<== inOrderEight2.
    Proof.
      (* ksimilar; equivList_app_tac. *) 
    Admitted.

  End Refinement2.

  Definition F2I := F2I addrSize dataBytes.
  Definition exec := exec addrSize dataBytes iExecName.
  Definition i2dEnq := i2dEnq addrSize dataBytes i2dName.
  Definition redirGet := redirGet addrSize.
  Definition redirectStr := redirectStr addrSize.

  Definition fi :=
    MODULE {
      Register "pc" : Bit addrSize <- Default

      with Rule "doFetch" :=
        Read pc <- "pc";
        Nondet predPc : SyntaxKind (Bit addrSize);
        Write "pc" <- #predPc;
        Call decEpoch <- decGetEpoch1();
        Call exeEpoch <- exeGetEpoch1();

        (* Instead of pushing, we directly use it! *)
        LET f2i <- STRUCT { "f2dOrig" ::= STRUCT { "pc" ::= #pc;
                                                   "predPc" ::= #predPc;
                                                   "decEpoch" ::= #decEpoch;
                                                   "exeEpoch" ::= #exeEpoch };
                            "iMemReq" ::= STRUCT { "addr" ::= #pc;
                                                   "op" ::= $$false;
                                                   "data" ::= $$Default }
                          };

        (* iMem part *)
        LET f2dOrig <- #f2i!F2I@."f2dOrig";
        LET req <- #f2i!F2I@."iMemReq";
        Call rep <- exec(#req);
        Call i2dEnq(STRUCT { "f2dOrig" ::= #f2dOrig;
                             "iMemRep" ::= #rep });
        (* iMem part ended *)
        
        Retv

      with Rule "doFetch_by_redirectExe" :=
        Call exeRedir <- (redirGet "exe")();
        Assert (#exeRedir!(Maybe (Struct redirectStr))@."isValid");
        LET r <- #exeRedir!(Maybe (Struct redirectStr))@."value";
        LET pc <- #r!redirectStr@."nextPc";
        Call exeToggleEpoch();
        Call (redirSetInvalid "exe")();
        Call (redirSetInvalid "dec")();

        Nondet predPc : SyntaxKind (Bit addrSize);
        Write "pc" <- #predPc;
        Call decEpoch <- decGetEpoch1();
        Call exeEpoch <- exeGetEpoch1();

        (* Instead of pushing, we directly use it! *)
        LET f2i <- STRUCT { "f2dOrig" ::= STRUCT { "pc" ::= #pc;
                                                   "predPc" ::= #predPc;
                                                   "decEpoch" ::= #decEpoch;
                                                   "exeEpoch" ::= #exeEpoch };
                            "iMemReq" ::= STRUCT { "addr" ::= #pc;
                                                   "op" ::= $$false;
                                                   "data" ::= $$Default }
                          };

        (* iMem part *)
        LET f2dOrig <- #f2i!F2I@."f2dOrig";
        LET req <- #f2i!F2I@."iMemReq";
        Call rep <- exec(#req);
        Call i2dEnq(STRUCT { "f2dOrig" ::= #f2dOrig;
                             "iMemRep" ::= #rep });
        (* iMem part ended *)
        
        Retv

      with Rule "doFetch_by_redirectDec" :=
        Call exeRedir <- (redirGet "exe")();
        Assert !(#exeRedir!(Maybe (Struct redirectStr))@."isValid");
        Call decRedir <- (redirGet "dec")();
        Assert (#decRedir!(Maybe (Struct redirectStr))@."isValid");
        LET r <- #decRedir!(Maybe (Struct redirectStr))@."value";
        LET pc <- #r!redirectStr@."nextPc";
        Call decToggleEpoch();
        Call (redirSetInvalid "dec")();

        Nondet predPc : SyntaxKind (Bit addrSize);
        Write "pc" <- #predPc;
        Call decEpoch <- decGetEpoch1();
        Call exeEpoch <- exeGetEpoch1();

        (* Instead of pushing, we directly use it! *)
        LET f2i <- STRUCT { "f2dOrig" ::= STRUCT { "pc" ::= #pc;
                                                   "predPc" ::= #predPc;
                                                   "decEpoch" ::= #decEpoch;
                                                   "exeEpoch" ::= #exeEpoch };
                            "iMemReq" ::= STRUCT { "addr" ::= #pc;
                                                   "op" ::= $$false;
                                                   "data" ::= $$Default }
                          };

        (* iMem part *)
        LET f2dOrig <- #f2i!F2I@."f2dOrig";
        LET req <- #f2i!F2I@."iMemReq";
        Call rep <- exec(#req);
        Call i2dEnq(STRUCT { "f2dOrig" ::= #f2dOrig;
                             "iMemRep" ::= #rep });
        (* iMem part ended *)
        
        Retv
    }.

  Definition inOrderEight3 :=
    (fi ++ (decRedir ++ exeRedir ++ decEpoch ++ exeEpoch ++
                     i2d ++ decodeNondet ++ d2r ++
                     regRead ++ rf ++ bypass ++ r2e ++
                     executeNondet ++ e2m ++
                     mem ++ m2d ++
                     dMem ++ d2w ++
                     writeback))%kami.
  
  Section Refinement3.

    Lemma fetchNondet_f2i_iMem_implements_fi:
      (fetchNondet ++ f2i ++ iMem)%kami <<== fi.
    Proof.
    Admitted.

    Theorem inOrderEight2_inOrderEight3: inOrderEight2 <<== inOrderEight3.
    Proof.
      kmodular_ex.
      - apply fetchNondet_f2i_iMem_implements_fi.
      - krefl.
    Qed.
      
  End Refinement3.  
  
End Processor.


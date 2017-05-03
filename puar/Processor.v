Require Import Kami Lib.Indexer.

Set Implicit Arguments.
Set Asymmetric Patterns.

Open Scope string.
Definition instRqToM := "instRqToM".
Definition instRpToP := "instRpToP".
Definition instRqVToP := "instRqVToP".
Definition instRpVToP := "instRpVToP".
Definition dataRqToM := "dataRqToM".
Definition dataRpToP := "dataRpToP".
Definition dataRqVToP := "dataRqVToP".
Definition dataRpVToP := "dataRpVToP".
                                     
Definition inst := "inst".
Definition instVToP := "instVToP".
Definition data := "data".
Definition dataVToP := "dataVToP".

Definition enq := "enq".
Definition deq := "deq".

Close Scope string.

Section Processor.
  Variable VAddr PAddr Inst RData CState Exception InstVToPRq InstVToPRp
           FetchRq FetchRp MemVToPRq MemVToPRp MemRq MemRp Data ByteEns Mode: Kind.
  Variable RIndexSz: nat.
  
  Definition RIndex := Bit RIndexSz.
  
  Variable getSrc1: forall ty, Inst @ ty -> RIndex @ ty.
  Variable getSrc2: forall ty, Inst @ ty -> RIndex @ ty.
  Variable getDst: forall ty, Inst @ ty -> RIndex @ ty.
  Variable execException: forall ty, Inst @ ty -> RData @ ty -> RData @ ty ->
                                     Exception @ ty.
  Variable execData: forall ty, Inst @ ty -> RData @ ty -> RData @ ty ->
                                RData @ ty.
  Variable cExecException: forall ty, Inst @ ty -> CState @ ty -> Mode @ ty -> Exception @ ty ->
                                      Exception @ ty.
  Variable cExecData: forall ty, Inst @ ty -> CState @ ty -> Mode @ ty -> Exception @ ty ->
                                 CState @ ty.
  Variable cExecExceptionPc: forall ty, Inst @ ty -> CState @ ty -> Mode @ ty ->
                                        Exception @ ty -> VAddr @ ty.

  Variable vAddr_InstVToPRq: forall ty, VAddr @ ty -> InstVToPRq @ ty.
  Variable instVToPRp_VAddr: forall ty, InstVToPRp @ ty -> VAddr @ ty.
  Variable instVToPRp_PAddr: forall ty, InstVToPRp @ ty -> PAddr @ ty.
  Variable instVToPRp_Mode: forall ty, InstVToPRp @ ty -> Mode @ ty.
  Variable instVToPRp_Exception: forall ty, InstVToPRp @ ty -> Exception @ ty.
  Variable pAddr_FetchRq: forall ty, PAddr @ ty -> FetchRq @ ty.
  Variable fetchRp_Inst: forall ty, FetchRp @ ty -> Inst @ ty.
  Variable fetchRp_PAddr: forall ty, FetchRp @ ty -> PAddr @ ty.
  Variable vAddr_MemVToPRq: forall ty, VAddr @ ty -> MemVToPRq @ ty.
  Variable memVToPRp_PAddr: forall ty, MemVToPRp @ ty -> PAddr @ ty.
  Variable memVToPRp_VAddr: forall ty, MemVToPRp @ ty -> VAddr @ ty.
  Variable pAddr_LdRq: forall ty, PAddr @ ty -> MemRq @ ty.
  Variable memRp_Data: forall ty, MemRp @ ty -> Data @ ty.
  Variable memRp_PAddr: forall ty, MemRp @ ty -> PAddr @ ty.
  Variable createStRq: forall ty, PAddr @ ty -> ByteEns @ ty -> Data @ ty -> MemRq @ ty.
  Variable data_VAddr: forall ty, Data @ ty -> VAddr @ ty.
  
  Definition instRqEnq := MethodSig (instRqToM -- enq) (FetchRq): Void.
  Definition instRpDeq := MethodSig (instRpToP -- deq) (Void): FetchRp.
  Definition instRqVToPEnq := MethodSig (instRqVToP -- enq) (InstVToPRq): Void.
  Definition instRpVToPDeq := MethodSig (instRpVToP -- deq) (Void): InstVToPRp.

  Definition memRqEnq := MethodSig (dataRqToM -- enq) (MemRq): Void.
  Definition memRpDeq := MethodSig (dataRpToP -- deq) (Void): MemRp.
  Definition memRqVToPEnq := MethodSig (dataRqVToP -- enq) (MemVToPRq): Void.
  Definition memRpVToPDeq := MethodSig (dataRpVToP -- deq) (Void): MemVToPRp.

  Definition commitInst := MethodSig inst (FetchRq): FetchRp.
  Definition commitInstVToP := MethodSig instVToP (InstVToPRq): InstVToPRp.
  Definition commitData := MethodSig data (MemRq): MemRp.
  Definition commitDataVToP := MethodSig dataVToP (MemVToPRq): MemVToPRp.

  Variable BtbState BpState: Kind.
  Variable BtbStateInit: ConstT BtbState.
  Variable BpStateInit: ConstT BpState.
  Variable RegFileInit: ConstT (Vector Data RIndexSz).
  Variable CStateInit: ConstT CState.
  Variable PcInit: ConstT VAddr.

  Variable getNextBtb: forall ty, BtbState @ ty -> VAddr @ ty -> VAddr @ ty.
  Variable updBtb: forall ty, BtbState @ ty -> VAddr @ ty -> VAddr @ ty -> BtbState @ ty.

  Variable getBp: forall ty, BpState @ ty -> VAddr @ ty -> Inst @ ty -> VAddr @ ty.
  Variable updBp: forall ty, BtbState @ ty -> VAddr @ ty -> Inst @ ty -> Bool @ ty ->
                             BpState @ ty.

  
  Open Scope string.
  Definition pc := "pc".
  Definition regFile := "regFile".
  Definition cState := "cState".
  Definition btb := "btb".
  Definition bp := "bp".
  Definition decEpoch := "decEpoch".
  Definition execEpoch := "execEpoch".
  Definition wbEpoch := "wbEpoch".
  Definition Valid := "Valid".
  Definition mode := "mode".
  Definition exception := "exception".

  Definition instVAddr := "instVAddr".
  Definition nextPc := "nextPc".
  Definition instPAddr := "instPAddr".

  Definition src1 := "src1".
  Definition src2 := "src2".
  Definition dst := "dst".
  
  Definition fifoInstVToPRq := "fifoInstVToPRq".
  Notation fifoInstVToPRqValid := (fifoInstVToPRq ++ Valid)%string.
  Definition fifoFetchRq := "fifoFetchRq".
  Notation fifoFetchRqValid := (fifoFetchRq ++ Valid)%string.
  Definition fifoFetchRp := "fifoFetchRp".
  Notation fifoFetchRpValid := (fifoFetchRp ++ Valid)%string.
  Definition fifoRegRead := "fifoRegRead".
  Notation fifoRegReadValid := (fifoRegRead ++ Valid)%string.
  
  Definition fifoExec := "fifoExec".
  Notation fifoExecValid := (fifoExec ++ Valid)%string.
  Definition fifoMemVToPRq := "fifoMemVToPRq".
  Notation fifoMemVToPRqValid := (fifoMemVToPRq ++ Valid)%string.
  Definition fifoMemRq := "fifoMemRq".
  Notation fifoMemRqValid := (fifoMemRq ++ Valid)%string.
  Definition fifoMemRp := "fifoMemRp".
  Notation fifoMemRpValid := (fifoMemRp ++ Valid)%string.

  Definition instVToPRq := "instVToPRq".
  Definition fetchRq := "fetchRq".
  Definition fetchRp := "fetchRp".
  Definition regRead := "regRead".
  Definition exec := "exec".
  Definition memVToPRq := "memVToPRq".
  Definition memRq := "memRq".
  Definition memRp := "memRp".
  Definition wb := "wb".
  Close Scope string.
  
  Notation "'Enq' f : kind <- v ; c" :=
    ( Read x : Bool <- (f ++ Valid)%string ;
      Assert ! #x ;
      Write f : kind <- v ;
      Write (f ++ Valid)%string <- $$ true ;
      c
    )%kami_sin
    (at level 12, right associativity, f at level 0, v at level 0) : kami_sin_scope.
  
  Notation "'Deq' v : kind <- f ; c" :=
    ( Read x : Bool <- (f ++ Valid)%string ;
      Assert #x ;
      Read v : kind <- f ;
      c
    )%kami_sin
    (at level 12, right associativity, f at level 0, v at level 0) : kami_sin_scope.

  Definition InstVToPRqT := STRUCT { decEpoch :: Bool;
                                     execEpoch :: Bool;
                                     wbEpoch :: Bool;
                                     nextPc :: VAddr}.

  Definition FetchRqT := STRUCT { decEpoch :: Bool;
                                  execEpoch :: Bool;
                                  wbEpoch :: Bool;
                                  mode :: Mode;
                                  exception :: Exception;
                                  instVAddr :: VAddr;
                                  nextPc :: VAddr
                                }.

  Definition FetchRpT := STRUCT { decEpoch :: Bool;
                                  execEpoch :: Bool;
                                  wbEpoch :: Bool;
                                  mode :: Mode;
                                  exception :: Exception;
                                  instVAddr :: VAddr;
                                  nextPc :: VAddr;
                                  instPAddr :: PAddr;
                                  inst :: Inst}.
                               
  Definition RegReadT := STRUCT { execEpoch :: Bool;
                                  wbEpoch :: Bool;
                                  mode :: Mode;
                                  exception :: Exception;
                                  instVAddr :: VAddr;
                                  nextPc :: VAddr;
                                  instPAddr :: PAddr;
                                  inst :: Inst;
                                  src1 :: Data;
                                  src2 :: Data
                                }.
  
  Definition ExecT := STRUCT { wbEpoch :: Bool;
                               mode :: Mode;
                               exception :: Exception;
                               instVAddr :: VAddr;
                               nextPc :: VAddr;
                               instPAddr :: PAddr;
                               inst :: Inst;
                               src1 :: Data;
                               src2 :: Data;
                               dst :: Data
                             }.

  Definition MemVToPRqT := STRUCT { wbEpoch :: Bool;
                                    mode :: Mode;
                                    exception :: Exception;
                                    instVAddr :: VAddr;
                                    nextPc :: VAddr;
                                    instPAddr :: PAddr;
                                    inst :: Inst;
                                    src1 :: Data;
                                    src2 :: Data;
                                    dst :: Data
                                  }.

  Definition MemRqT := STRUCT { wbEpoch :: Bool;
                                mode :: Mode;
                                exception :: Exception;
                                instVAddr :: VAddr;
                                nextPc :: VAddr;
                                instPAddr :: PAddr;
                                inst :: Inst;
                                src1 :: Data;
                                src2 :: Data;
                                dst :: Data
                              }.

  Definition MemRpT := STRUCT { wbEpoch :: Bool;
                                mode :: Mode;
                                exception :: Exception;
                                instVAddr :: VAddr;
                                nextPc :: VAddr;
                                instPAddr :: PAddr;
                                inst :: Inst;
                                src1 :: Data;
                                src2 :: Data;
                                dst :: Data
			      }.
  
  
  Definition processor :=
    SIN {
        Register pc : VAddr <- PcInit
        with Register regFile : Vector Data RIndexSz <- RegFileInit
        with Register cState : CState <- CStateInit
                                        
        with Register btb : BtbState <- BtbStateInit
        with Register bp : BpState <- BpStateInit

        with Register decEpoch: Bool <- (ConstBool false)
        with Register execEpoch : Bool <- (ConstBool false)
        with Register wbEpoch : Bool <- (ConstBool false)

        with Register fifoInstVToPRq : Struct InstVToPRqT <- Default
        with Register fifoInstVToPRqValid : Bool <- (ConstBool false)
                                             
        with Register fifoFetchRq : Struct FetchRqT <- Default
        with Register fifoFetchRqValid : Bool <- (ConstBool false)

        with Register fifoFetchRp : Struct FetchRpT <- Default
        with Register fifoFetchRpValid : Bool <- (ConstBool false)
                                    
        with Register fifoRegRead : Struct RegReadT <- Default
        with Register fifoRegReadValid : Bool <- (ConstBool false)
                                    
        with Register fifoExec : Struct ExecT <- Default
        with Register fifoExecValid : Bool <- (ConstBool false)

        with Register fifoMemVToPRq : Struct MemVToPRqT <- Default
        with Register fifoMemVToPRqValid : Bool <- (ConstBool false)

        with Register fifoMemRq : Struct MemRqT <- Default
        with Register fifoMemRqValid : Bool <- (ConstBool false)

        with Register fifoMemRp : Struct MemRpT <- Default
        with Register fifoMemRpValid : Bool <- (ConstBool false)

        with Rule instVToPRq :=
          Read pcVal <- pc;
          Read decEpochVal <- decEpoch;
          Read execEpochVal <- execEpoch;
          Read wbEpochVal <- wbEpoch;
          Read btbStateVal <- btb;
          LET nextPcVal <- getNextBtb #btbStateVal #pcVal;
          Enq fifoInstVToPRq : Struct InstVToPRqT <- (STRUCT {
                                                          decEpoch ::= #decEpochVal;
                                                          execEpoch ::= #execEpochVal;
                                                          wbEpoch ::= #wbEpochVal;
                                                          nextPc ::= #nextPcVal}) ;
          Call instRqVToPEnq(vAddr_InstVToPRq #pcVal);
          Retv

        with Rule fetchRq :=
          Deq inp1 : Struct InstVToPRqT <- fifoInstVToPRq;
          Call inp2 <- instRpVToPDeq();
          Enq fifoFetchRq : Struct FetchRqT <- (STRUCT {
                                                    decEpoch ::= #inp1!InstVToPRqT@.decEpoch;
                                                    execEpoch ::= #inp1!InstVToPRqT@.execEpoch;
                                                    wbEpoch ::= #inp1!InstVToPRqT@.wbEpoch;
                                                    mode ::= instVToPRp_Mode #inp2;
                                                    exception ::= instVToPRp_Exception #inp2;
                                                    instVAddr ::= instVToPRp_VAddr #inp2;
                                                    nextPc ::= #inp1!InstVToPRqT@.nextPc });
          Call instRqEnq(pAddr_FetchRq (instVToPRp_PAddr #inp2));
          Retv

        with Rule fetchRp :=
          Deq inp1 : Struct FetchRqT <- fifoFetchRq;
          Call inp2 <- instRpDeq();
          Enq fifoFetchRp : Struct FetchRpT <- (STRUCT {
                                                    decEpoch ::= #inp1!FetchRqT@.decEpoch;
                                                    execEpoch ::= #inp1!FetchRqT@.execEpoch;
                                                    wbEpoch ::= #inp1!FetchRqT@.wbEpoch;
                                                    mode ::= #inp1!FetchRqT@.mode;
                                                    exception ::= #inp1!FetchRqT@.exception;
                                                    instVAddr ::= #inp1!FetchRqT@.instVAddr;
                                                    nextPc ::= #inp1!FetchRqT@.nextPc;
                                                    instPAddr ::= fetchRp_PAddr #inp2;
                                                    inst ::= fetchRp_Inst #inp2
                                               });
          Retv

      }.

End Processor.

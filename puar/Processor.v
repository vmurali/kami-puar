Require Import Kami Lib.Indexer.

Set Implicit Arguments.
Set Asymmetric Patterns.

Open Scope string.
Definition instRqToM := "instRqToM".
Definition instRpToP := "instRpToP".
Definition instRqVToP := "instRqVToP".
Definition instRpVToP := "instRpVToP".
Definition ldRqToM := "ldRqToM".
Definition ldRpToP := "ldRpToP".
Definition stRqToM := "stRqToM".
Definition dataRqVToP := "dataRqVToP".
Definition dataRpVToP := "dataRpVToP".
                                     
Definition inst := "inst".
Definition instVToP := "instVToP".
Definition data := "data".
Definition dataVToP := "dataVToP".

Definition enq := "enq".
Definition deq := "deq".
Definition exception := "exception".

Definition commitVpc := "commitVpc".
Definition commitPc := "commitPc".
Definition commitInst := "commitInst".
Definition commitSrc1 := "commitSrc1".
Definition commitSrc2 := "commitSrc2".
Definition commitLdPAddr := "commitLdPAddr".
Definition commitLdData := "commitLdData".
Definition commitMode := "commitMode".
Definition commitException := "commitException".
Definition commitNextPc := "commitNextPc".
Definition commitNextMode := "commitNextMode".

Definition pc := "pc".
Definition wbPc := "wbPc".
Definition regFile := "regFile".
Definition cState := "cState".
Definition btb := "btb".
Definition bp := "bp".
Definition decEpoch := "decEpoch".
Definition execEpoch := "execEpoch".
Definition wbEpoch := "wbEpoch".
Definition Valid := "Valid".
Definition mode := "mode".
Definition instMode := "instMode".
Definition dataMode := "dataMode".

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
Definition fifoLdRq := "fifoLdRq".
Notation fifoLdRqValid := (fifoLdRq ++ Valid)%string.
Definition fifoLdRp := "fifoLdRp".
Notation fifoLdRpValid := (fifoLdRp ++ Valid)%string.

Definition instVToPRq := "instVToPRq".
Definition fetchRq := "fetchRq".
Definition fetchRp := "fetchRp".
Definition regRead := "regRead".
Definition exec := "exec".
Definition memVToPRq := "memVToPRq".
Definition memRq := "memRq".
Definition memRp := "memRp".
Definition wb := "wb".
Definition commit := "commit".

Close Scope string.

Section Processor.
  Variable VAddr PAddr Inst RData CState Exception InstVToPRq InstVToPRp
           FetchRq FetchRp MemVToPRq MemVToPRp LdRq LdRp StRq Data ByteEns Mode: Kind.
  Variable RIndexSz: nat.

  Variable BtbState BpState: Kind.
  Variable BtbStateInit: ConstT BtbState.
  Variable BpStateInit: ConstT BpState.
  Variable RegFileInit: ConstT (Vector Data RIndexSz).
  Variable CStateInit: ConstT CState.
  Variable PcInit: ConstT VAddr.
  Variable ModeInit: ConstT Mode.

  Definition RIndex := Bit RIndexSz.
  
  Variable getSrc1: forall ty, Inst @ ty -> RIndex @ ty.
  Variable getSrc2: forall ty, Inst @ ty -> RIndex @ ty.
  Variable getDst: forall ty, Inst @ ty -> RIndex @ ty.
  Variable execException: forall ty, Inst @ ty -> RData @ ty -> RData @ ty ->
                                     Exception @ ty.
  Variable execData: forall ty, Inst @ ty -> RData @ ty -> RData @ ty ->
                                RData @ ty.
  Variable cExecException: forall ty, Inst @ ty -> VAddr @ ty -> VAddr @ ty -> CState @ ty ->
                                      Mode @ ty ->
                                      Exception @ ty ->
                                      Mode @ ty -> Mode @ ty -> Exception @ ty.
  Variable cExecState: forall ty, Inst @ ty -> VAddr @ ty -> VAddr @ ty -> CState @ ty ->
                                  Mode @ ty ->
                                  Exception @ ty ->
                                  Mode @ ty -> Mode @ ty -> CState @ ty.
  Variable cExecPc: forall ty, Inst @ ty -> VAddr @ ty -> VAddr @ ty -> CState @ ty ->
                               Mode @ ty ->
                               Exception @ ty -> Mode @ ty -> Mode @ ty -> VAddr @ ty.
  Variable cExecMode: forall ty, Inst @ ty -> VAddr @ ty -> VAddr @ ty -> CState @ ty ->
                                 Mode @ ty ->
                                 Exception @ ty -> Mode @ ty -> Mode @ ty -> Mode @ ty.
  Variable isLd: forall ty, Inst @ ty -> Bool @ ty.
  Variable isSt: forall ty, Inst @ ty -> Bool @ ty.
  Variable modeLe: forall ty, Mode @ ty -> Mode @ ty -> Bool @ ty.
  Variable noException: forall ty, Exception @ ty -> Bool @ ty.

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
  Variable pAddr_LdRq: forall ty, PAddr @ ty -> LdRq @ ty.
  Variable ldRp_Data: forall ty, LdRp @ ty -> Data @ ty.
  Variable ldRp_PAddr: forall ty, LdRp @ ty -> PAddr @ ty.
  Variable createStRq: forall ty, PAddr @ ty -> ByteEns @ ty -> Data @ ty -> StRq @ ty.
  Variable data_VAddr: forall ty, Data @ ty -> VAddr @ ty.
  Variable vAddr_Data: forall ty, VAddr @ ty -> Data @ ty.
  
  Variable getNextBtb: forall ty, BtbState @ ty -> VAddr @ ty -> VAddr @ ty.
  Variable updBtb: forall ty, BtbState @ ty -> VAddr @ ty -> VAddr @ ty -> BtbState @ ty.

  Variable getBp: forall ty, BpState @ ty -> VAddr @ ty -> Inst @ ty -> VAddr @ ty.
  Variable updBp: forall ty, BtbState @ ty -> VAddr @ ty -> Inst @ ty -> Bool @ ty ->
                             BpState @ ty.
  
  Definition instRqEnq := MethodSig (instRqToM -- enq) (FetchRq): Void.
  Definition instRpDeq := MethodSig (instRpToP -- deq) (Void): FetchRp.
  Definition instRqVToPEnq := MethodSig (instRqVToP -- enq) (InstVToPRq): Void.
  Definition instRpVToPDeq := MethodSig (instRpVToP -- deq) (Void): InstVToPRp.

  Definition ldRqEnq := MethodSig (ldRqToM -- enq) (LdRq): Void.
  Definition stRqEnq := MethodSig (stRqToM -- enq) (StRq): Void.
  Definition ldRpDeq := MethodSig (ldRpToP -- deq) (Void): LdRp.
  Definition memRqVToPEnq := MethodSig (dataRqVToP -- enq) (MemVToPRq): Void.
  Definition memRpVToPDeq := MethodSig (dataRpVToP -- deq) (Void): MemVToPRp.

  Definition CommitT := STRUCT
    { commitVpc :: VAddr;
      commitPc :: PAddr;
      commitInst :: Inst;
      commitSrc1 :: Data;
      commitSrc2 :: Data;
      commitLdPAddr :: PAddr;
      commitLdData :: Data;
      commitMode :: Mode;
      commitException :: Exception;
      commitNextPc :: VAddr;
      commitNextMode :: Mode }.

  Definition commitLabel := MethodSig commit (Struct CommitT): Void.

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
                                  instMode :: Mode;
                                  exception :: Exception;
                                  instVAddr :: VAddr;
                                  nextPc :: VAddr
                                }.

  Definition FetchRpT := STRUCT { decEpoch :: Bool;
                                  execEpoch :: Bool;
                                  wbEpoch :: Bool;
                                  instMode :: Mode;
                                  exception :: Exception;
                                  instVAddr :: VAddr;
                                  nextPc :: VAddr;
                                  instPAddr :: PAddr;
                                  inst :: Inst}.
                               
  Definition RegReadT := STRUCT { execEpoch :: Bool;
                                  wbEpoch :: Bool;
                                  instMode :: Mode;
                                  exception :: Exception;
                                  instVAddr :: VAddr;
                                  nextPc :: VAddr;
                                  instPAddr :: PAddr;
                                  inst :: Inst;
                                  src1 :: Data;
                                  src2 :: Data
                                }.
  
  Definition ExecT := STRUCT { wbEpoch :: Bool;
                               instMode :: Mode;
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
                                    instMode :: Mode;
                                    exception :: Exception;
                                    instVAddr :: VAddr;
                                    nextPc :: VAddr;
                                    instPAddr :: PAddr;
                                    inst :: Inst;
                                    src1 :: Data;
                                    src2 :: Data;
                                    dst :: Data
                                  }.

  Definition LdRqT := STRUCT { wbEpoch :: Bool;
                               instMode :: Mode;
                               exception :: Exception;
                               instVAddr :: VAddr;
                               nextPc :: VAddr;
                               instPAddr :: PAddr;
                               inst :: Inst;
                               src1 :: Data;
                               src2 :: Data;
                               dst :: Data;
                               dataMode :: Mode
                             }.

  Definition LdRpT := STRUCT { wbEpoch :: Bool;
                               instMode :: Mode;
                               exception :: Exception;
                               instVAddr :: VAddr;
                               nextPc :: VAddr;
                               instPAddr :: PAddr;
                               inst :: Inst;
                               src1 :: Data;
                               src2 :: Data;
                               dst :: Data;
                               dataMode :: Mode
			     }.
  
  
  Definition processor :=
    SIN {
        Register pc : VAddr <- PcInit
        with Register mode : Mode <- ModeInit
        with Register wbPc : VAddr <- PcInit
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

        with Register fifoLdRq : Struct LdRqT <- Default
        with Register fifoLdRqValid : Bool <- (ConstBool false)

        with Register fifoLdRp : Struct LdRpT <- Default
        with Register fifoLdRpValid : Bool <- (ConstBool false)

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
                                                    instMode ::= instVToPRp_Mode #inp2;
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
                                                    instMode ::= #inp1!FetchRqT@.instMode;
                                                    exception ::= #inp1!FetchRqT@.exception;
                                                    instVAddr ::= #inp1!FetchRqT@.instVAddr;
                                                    nextPc ::= #inp1!FetchRqT@.nextPc;
                                                    instPAddr ::= fetchRp_PAddr #inp2;
                                                    inst ::= fetchRp_Inst #inp2
                                               });
          Retv

        with Rule wb :=
          Deq inp1 : Struct LdRpT <- fifoLdRp;
          Read wbEpochVal <- wbEpoch;
          Read wbPcVal <- wbPc;
          Read cStateVal <- cState;
          Read modeVal <- mode;
          LET epochMatch <- #inp1!LdRpT@.wbEpoch == #wbEpochVal;
          LET pcMatch <- #inp1!LdRpT@.instVAddr == #wbPcVal;
          LET wbExcept <- cExecException #inp1!LdRpT@.inst #inp1!LdRpT@.instVAddr
              #inp1!LdRpT@.nextPc #cStateVal #inp1!LdRpT@.mode #inp1!LdRpT@.exception
              #inp1!LdRpT@.instMode #inp1!LdRpT@.dataMode;
          LET cStateNew <- cExecState #inp1!LdRpT@.inst #inp1!LdRpT@.instVAddr
              #inp1!LdRpT@.nextPc #cStateVal #inp1!LdRpT@.mode #inp1!LdRpT@.exception
              #inp1!LdRpT@.instMode #inp1!LdRpT@.dataMode;
          LET newPc <- cExecPc #inp1!LdRpT@.inst
              #inp1!LdRpT@.instVAddr
              #inp1!LdRpT@.nextPc 
              #cStateVal #inp1!LdRpT@.mode #inp1!LdRpT@.exception
              #inp1!LdRpT@.instMode #inp1!LdRpT@.dataMode;
          LET newMode <- cExecMode #inp1!LdRpT@.inst
              #inp1!LdRpT@.instVAddr
              #inp1!LdRpT@.nextPc 
              #cStateVal #inp1!LdRpT@.mode #inp1!LdRpT@.exception
              #inp1!LdRpT@.instMode #inp1!LdRpT@.dataMode;

          If isLd #inp1!LdRpT@.inst
          then ( Call inp2 <- ldRpDeq();
                 Ret #inp2 )
          else Ret $$ Default
          as ldRp;
          LET ldPAddr <- ldRp_PAddr #ldRp;
          LET ldData <- ldRp_Data #ldRp;
          
          If #epochMatch && #pcMatch
          then (
            Write cState <- #cStateNew;
            Write wbPc <- #newPc;
            Write mode <- #newMode;
            If #newPc != #inp1!LdRpT@.nextPc
            then (
              Write wbEpoch <- ! #wbEpochVal;
              Write pc <- #newPc;
              Retv
            );
            Call commitLabel (STRUCT {
                                  commitVpc ::= #inp1!LdRpT@.instVAddr;
                                  commitPc ::= #inp1!LdRpT@.instPAddr;
                                  commitInst ::= #inp1!LdRpT@.inst;
                                  commitSrc1 ::= #inp1!LdRpT@.src1;
                                  commitSrc2 ::= #inp1!LdRpT@.src2;
                                  commitLdPAddr ::= #ldPAddr;
                                  commitLdData ::= #ldData;
                                  commitMode ::= #modeVal;
                                  commitException ::= #wbExcept;
                                  commitNextPc ::= #newPc;
                                  commitNextMode ::= #newMode });
            
            If isSt #inp1!LdRqT@.inst && noException #wbExcept
            then ( Call stRqEnq();
                   Retv );
            Retv  
          );
          Retv
      }.
End Processor.

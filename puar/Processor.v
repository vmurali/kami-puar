Require Import Kami Lib.Indexer.

Set Implicit Arguments.
Set Asymmetric Patterns.

Open Scope string.
Definition msg := "msg".
Definition instRqToM := "instRqToM".
Definition instRpToP := "instRpToP".
Definition instRqVToP := "instRqVToP".
Definition instRpVToP := "instRpVToP".
Definition rqToM := "rqToM".
Definition ldRpToP := "ldRpToP".
Definition dataRqVToP := "dataRqVToP".
Definition dataRpVToP := "dataRpVToP".
Definition setAccessInstVToP := "setAccessInstVToP".
Definition setAccessDataVToP := "setAccessDataVToP".
Definition setDirtyDataVToP := "setDirtyDataVToP".

Definition inst := "inst".
Definition instVToP := "instVToP".
Definition data := "data".
Definition dataVToP := "dataVToP".

Definition execException := "execException".
Definition execNextPc := "execNextPc".
Definition execVAddr := "execVAddr".
Definition execData := "execData".

Definition enq := "enq".
Definition deq := "deq".
Definition exception := "exception".

Definition vAddr := "vAddr".
Definition pAddr := "pAddr".

Definition commitVpc := "commitVpc".
Definition commitPc := "commitPc".
Definition commitInst := "commitInst".
Definition commitDst := "commitDst".
Definition commitVAddr := "commitVAddr".
Definition commitPAddr := "commitPAddr".
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
Definition fifoLdRq := "fifoLdRq".
Notation fifoLdRqValid := (fifoLdRq ++ Valid)%string.
Definition fifoLdRp := "fifoLdRp".
Notation fifoLdRpValid := (fifoLdRp ++ Valid)%string.

Definition instVToPRq := "instVToPRq".
Definition fetchRq := "fetchRq".
Definition fetchRp := "fetchRp".
Definition regRead := "regRead".
Definition exec := "exec".
Definition ldRq := "ldRq".
Definition ldRp := "ldRp".
Definition wb := "wb".
Definition commit := "commit".

Definition newCState := "newCState".
Definition newMode := "newMode".
Definition newPc := "newPc".
Definition currException := "currException".

Close Scope string.

Notation "e1 ? e2 : e3" := (ITE e1 e2 e3) (at level 12) : kami_expr_scope.


Section Processor.
  Variable VAddr PAddr Inst Data CState Exception InstVToPRq InstVToPRp
           FetchRq FetchRp MemVToPRq MemVToPRp MemRq LdRp ByteEns Mode: Kind.
  Variable RIndexSz: nat.

  Variable BtbState BpState: Kind.
  Variable BtbStateInit: ConstT BtbState.
  Variable BpStateInit: ConstT BpState.
  Variable RegFileInit: ConstT (Vector Data RIndexSz).
  Variable CStateInit: ConstT CState.
  Variable PcInit: ConstT VAddr.
  Variable ModeInit: ConstT Mode.

  Notation RIndex := (Bit RIndexSz).
  Definition CExec := STRUCT
                        { newCState :: CState;
                          newPc :: VAddr;
                          newMode :: Mode;
                          currException :: Exception }.
  
  Definition Exec := STRUCT
                       { execException :: Exception;
                         execNextPc :: VAddr;
                         execVAddr :: VAddr;
                         execData :: Data }.
  
  Variable getSrc1: forall ty, Inst @ ty -> RIndex @ ty.
  Variable getSrc2: forall ty, Inst @ ty -> RIndex @ ty.
  Variable useSrc1: forall ty, Inst @ ty -> Bool @ ty.
  Variable useSrc2: forall ty, Inst @ ty -> Bool @ ty.
  Variable getDst: forall ty, Inst @ ty -> RIndex @ ty.
  Variable execFn: forall ty, Inst @ ty -> Data @ ty -> Data @ ty ->
                              Exception @ ty -> (Struct Exec) @ ty.
  Variable cExec: forall ty,  Inst @ ty -> VAddr @ ty -> VAddr @ ty -> CState @ ty ->
                              Mode @ ty -> Exception @ ty -> Mode @ ty -> Mode @ ty ->
                              (Struct CExec) @ ty.
  Variable isLd: forall ty, Inst @ ty -> Bool @ ty.
  Variable isSt: forall ty, Inst @ ty -> Bool @ ty.
  Variable isNotZero: forall ty, RIndex @ ty -> Bool @ ty.
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
  Variable memVToPRp_Mode: forall ty, MemVToPRp @ ty -> Mode @ ty.
  Variable pAddr_LdRq: forall ty, PAddr @ ty -> MemRq @ ty.
  Variable ldRp_Data: forall ty, LdRp @ ty -> Data @ ty.
  Variable ldRp_PAddr: forall ty, LdRp @ ty -> PAddr @ ty.
  Variable createStRq: forall ty, VAddr @ ty -> Data @ ty -> MemRq @ ty.
  
  Variable getNextBtb: forall ty, BtbState @ ty -> VAddr @ ty -> VAddr @ ty.
  Variable updBtb: forall ty, BtbState @ ty -> VAddr @ ty -> VAddr @ ty -> BtbState @ ty.

  Variable getBp: forall ty, BpState @ ty -> VAddr @ ty -> Inst @ ty -> VAddr @ ty.
  Variable updBp: forall ty, BtbState @ ty -> VAddr @ ty -> Inst @ ty -> Bool @ ty ->
                             BpState @ ty.

  Definition isLdSt ty (inst : Inst @ ty) := (isLd inst || isSt inst)%kami_expr.
  Definition isNm ty (inst : Inst @ ty) := (!(isLdSt inst))%kami_expr.
  
  Definition instRqEnq := MethodSig (instRqToM -- enq) (FetchRq): Void.
  Definition instRpDeq := MethodSig (instRpToP -- deq) (Void): FetchRp.
  Definition instRqVToPEnq := MethodSig (instRqVToP -- enq) (InstVToPRq): Void.
  Definition instRpVToPDeq := MethodSig (instRpVToP -- deq) (Void): InstVToPRp.

  Definition memRqEnq := MethodSig (rqToM -- enq) (MemRq): Void.
  Definition ldRpDeq := MethodSig (ldRpToP -- deq) (Void): LdRp.
  Definition memRqVToPEnq := MethodSig (dataRqVToP -- enq) (MemVToPRq): Void.
  Definition memRpVToPDeq := MethodSig (dataRpVToP -- deq) (Void): MemVToPRp.
  Definition setAccessInstVToPCall := MethodSig setAccessInstVToP (VAddr): Void.
  Definition setAccessDataVToPCall := MethodSig setAccessDataVToP (VAddr): Void.
  Definition setDirtyDataVToPCall := MethodSig setDirtyDataVToP (VAddr): Void.

  
  Definition CommitT := STRUCT
    { commitVpc :: VAddr;
      commitPc :: PAddr;
      commitInst :: Inst;
      commitDst :: Data;
      commitVAddr :: VAddr;
      commitPAddr :: PAddr;
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
  
  Notation "'Pop' v : kind <- f ; c" :=
    ( Read x : Bool <- (f ++ Valid)%string ;
      Assert #x ;
      Read v : kind <- f ;
      Write (f ++ Valid)%string <- $$ false ;
      c
    )%kami_sin
    (at level 12, right associativity, f at level 0, v at level 0) : kami_sin_scope.

  Notation "'Deq' f ; c" :=
    ( Read x : Bool <- (f ++ Valid)%string ;
      Assert #x ;
      Write (f ++ Valid)%string <- $$ false ;
      c
    )%kami_sin
    (at level 12, right associativity, f at level 0) : kami_sin_scope.

  Notation "'First' v : kind <- f ; c" :=
    ( Read x : Bool <- (f ++ Valid)%string ;
      Assert #x ;
      Read v : kind <- f ;
      c
    )%kami_sin
    (at level 12, right associativity, f at level 0, v at level 0) : kami_sin_scope.

  Definition InstVToPRqT := STRUCT { decEpoch :: Bool;
                                     execEpoch :: Bool;
                                     wbEpoch :: Bool;
                                     instVAddr :: VAddr;
                                     nextPc :: VAddr
                                   }.
                                     

  Definition FetchRqT := STRUCT { decEpoch :: Bool;
                                  execEpoch :: Bool;
                                  wbEpoch :: Bool;
                                  instVAddr :: VAddr;
                                  nextPc :: VAddr;
                                  instMode :: Mode;
                                  exception :: Exception;
                                  instPAddr :: PAddr
                                }.

  Definition RegReadT := STRUCT { execEpoch :: Bool;
                                  wbEpoch :: Bool;
                                  instVAddr :: VAddr;
                                  nextPc :: VAddr;
                                  instMode :: Mode;
                                  exception :: Exception;
                                  instPAddr :: PAddr;
                                  inst :: Inst;
                                  src1 :: Data;
                                  src2 :: Data
                                }.
  
  Definition ExecT := STRUCT { wbEpoch :: Bool;
                               instVAddr :: VAddr;
                               nextPc :: VAddr;
                               instMode :: Mode;
                               exception :: Exception;
                               instPAddr :: PAddr;
                               inst :: Inst;
                               vAddr :: VAddr;
                               dst :: Data (* Serves as data for store also *)
                             }.

  Definition LdRqT := STRUCT { wbEpoch :: Bool;
                               instVAddr :: VAddr;
                               nextPc :: VAddr;
                               instMode :: Mode;
                               exception :: Exception;
                               instPAddr :: PAddr;
                               inst :: Inst;
                               vAddr :: VAddr;
                               dst :: Data; (* Serves as data for store also *)
                               pAddr :: PAddr;
                               dataMode :: Mode
                             }.

  Definition bypass ty (f1Valid f2Valid f3Valid: Bool @ ty)
             (f1 f2 f3: Inst @ ty) (f1d f2d f3d d: Data @ ty) (src: RIndex @ ty) :=
    ( IF (f1Valid && isNm f1 && isNotZero (getDst f1) && getDst f1 == src)
      then f1d else
      IF (f2Valid && isNm f2 && isNotZero (getDst f2) && getDst f2 == src)
      then f2d else
      IF (f3Valid && isNm f3 && isNotZero (getDst f3) && getDst f3 == src)
      then f3d else d
    )%kami_expr.
  
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

        with Register fifoFetchRp : Struct FetchRqT <- Default
        with Register fifoFetchRpValid : Bool <- (ConstBool false)
                                    
        with Register fifoRegRead : Struct RegReadT <- Default
        with Register fifoRegReadValid : Bool <- (ConstBool false)
                                    
        with Register fifoExec : Struct ExecT <- Default
        with Register fifoExecValid : Bool <- (ConstBool false)

        with Register fifoLdRq : Struct LdRqT <- Default
        with Register fifoLdRqValid : Bool <- (ConstBool false)

        with Register fifoLdRp : Struct LdRqT <- Default
        with Register fifoLdRpValid : Bool <- (ConstBool false)

        with Rule instVToPRq :=
          Read pcVal <- pc;
          Read decEpochVal <- decEpoch;
          Read execEpochVal <- execEpoch;
          Read wbEpochVal <- wbEpoch;
          Read btbStateVal <- btb;
          LET nextPcVal <- getNextBtb #btbStateVal #pcVal;
          Write pc <- #nextPcVal;
          Enq fifoInstVToPRq : Struct InstVToPRqT <-
                                      (STRUCT {
                                           decEpoch ::= #decEpochVal;
                                           execEpoch ::= #execEpochVal;
                                           wbEpoch ::= #wbEpochVal;
                                           instVAddr ::= #pcVal;
                                           nextPc ::= #nextPcVal });
          Call instRqVToPEnq(vAddr_InstVToPRq #pcVal);
          Retv

        with Rule fetchRq :=
          Pop inp1 : Struct InstVToPRqT <- fifoInstVToPRq;
          Call inp2 <- instRpVToPDeq();
          Enq fifoFetchRq : Struct FetchRqT <-
                                   (STRUCT {
                                        decEpoch ::= #inp1!InstVToPRqT@.decEpoch;
                                        execEpoch ::= #inp1!InstVToPRqT@.execEpoch;
                                        wbEpoch ::= #inp1!InstVToPRqT@.wbEpoch;
                                        instVAddr ::= #inp1!InstVToPRqT@.instVAddr;
                                        nextPc ::= #inp1!InstVToPRqT@.nextPc;
                                        instMode ::= instVToPRp_Mode #inp2;
                                        exception ::= instVToPRp_Exception #inp2;
                                        instPAddr ::= instVToPRp_PAddr #inp2 });
          Call instRqEnq(pAddr_FetchRq (instVToPRp_PAddr #inp2));
          Retv

        with Rule fetchRp :=
          Pop inp1 : Struct FetchRqT <- fifoFetchRq;
          Enq fifoFetchRp : Struct FetchRqT <- #inp1;
          Retv

        with Rule regRead :=
          Pop inp1 : Struct FetchRqT <- fifoFetchRp;
          Call inp2 <- instRpDeq();
          Read decEpochVal <- decEpoch;
          Read execEpochVal <- execEpoch;
          Read wbEpochVal <- wbEpoch;
          Read bpStateVal <- bp;
          If #decEpochVal == #inp1!FetchRqT@.decEpoch &&
             #execEpochVal == #inp1!FetchRqT@.execEpoch &&
             #wbEpochVal == #inp1!FetchRqT@.wbEpoch                               
          then (
            Read regFileVal <- regFile;
            LET instVal <- fetchRp_Inst #inp2;    
            LET src1Val <- #regFileVal@[getSrc1 #instVal];
            LET src2Val <- #regFileVal@[getSrc2 #instVal];
            LET nextPcVal <- getBp #bpStateVal #inp1!FetchRqT@.instVAddr #instVal;
            If #nextPcVal != #inp1!FetchRqT@.nextPc
            then (
              Write pc <- #nextPcVal;
              Write decEpoch <- ! #decEpochVal;
              Retv
              );
            Enq fifoRegRead : Struct RegReadT <-
                                     (STRUCT {
                                          execEpoch ::= #inp1!FetchRqT@.execEpoch;
                                          wbEpoch ::= #inp1!FetchRqT@.wbEpoch;
                                          instVAddr ::= #inp1!FetchRqT@.instVAddr;
                                          nextPc ::= #nextPcVal;
                                          instMode ::= #inp1!FetchRqT@.instMode;
                                          exception ::= #inp1!FetchRqT@.exception;
                                          instPAddr ::= #inp1!FetchRqT@.instPAddr;
                                          inst ::= #instVal;
                                          src1 ::= #src1Val;
                                          src2 ::= #src2Val });
            Retv
            );
          Retv

        with Rule exec :=
          Pop inp1 : Struct RegReadT <- fifoRegRead;
          Read execEpochVal <- execEpoch;
          Read wbEpochVal <- wbEpoch;
          If #execEpochVal == #inp1!RegReadT@.execEpoch &&
             #wbEpochVal == #inp1!RegReadT@.wbEpoch                               
          then (
            Read fifoExecData <- fifoExec;
            Read fifoLdRqData <- fifoLdRq;
            Read fifoLdRpData <- fifoLdRp;
            Read fifoExecV <- fifoExecValid;
            Read fifoLdRqV <- fifoLdRqValid;
            Read fifoLdRpV <- fifoLdRpValid;

            LET stall <- (#fifoExecV && isLd #fifoExecData!ExecT@.inst &&
                          isNotZero (getDst #fifoExecData!ExecT@.inst) &&
                          ((useSrc1 #inp1!RegReadT@.inst &&
                            getDst #fifoExecData!ExecT@.inst == getSrc1 #inp1!RegReadT@.inst) ||
                           (useSrc2 #inp1!RegReadT@.inst &&
                            getDst #fifoExecData!ExecT@.inst == getSrc2 #inp1!RegReadT@.inst))) ||
                         (#fifoLdRqV && isLd #fifoLdRqData!LdRqT@.inst &&
                          isNotZero (getDst #fifoLdRqData!LdRqT@.inst) &&
                          ((useSrc1 #inp1!RegReadT@.inst &&
                            getDst #fifoLdRqData!LdRqT@.inst == getSrc1 #inp1!RegReadT@.inst) ||
                           (useSrc2 #inp1!RegReadT@.inst &&
                            getDst #fifoLdRqData!LdRqT@.inst == getSrc2 #inp1!RegReadT@.inst))) ||
                         (#fifoLdRpV && isLd #fifoLdRpData!LdRqT@.inst &&
                          isNotZero (getDst #fifoLdRpData!LdRqT@.inst) &&
                          ((useSrc1 #inp1!RegReadT@.inst &&
                            getDst #fifoLdRpData!LdRqT@.inst == getSrc1 #inp1!RegReadT@.inst) ||
                           (useSrc2 #inp1!RegReadT@.inst &&
                            getDst #fifoLdRpData!LdRqT@.inst == getSrc1 #inp1!RegReadT@.inst)));

            Assert ! #stall;

            LET bypassSrc1 <-
                bypass
                #fifoExecV #fifoLdRqV #fifoLdRpV
                #fifoExecData!ExecT@.inst #fifoLdRqData!LdRqT@.inst #fifoLdRpData!LdRqT@.inst
                #fifoExecData!ExecT@.dst #fifoLdRqData!LdRqT@.dst #fifoLdRpData!LdRqT@.dst
                #inp1!RegReadT@.src1 (getSrc1 #inp1!RegReadT@.inst);

            LET bypassSrc2 <-
                bypass
                #fifoExecV #fifoLdRqV #fifoLdRpV
                #fifoExecData!ExecT@.inst #fifoLdRqData!LdRqT@.inst #fifoLdRpData!LdRqT@.inst
                #fifoExecData!ExecT@.dst #fifoLdRqData!LdRqT@.dst #fifoLdRpData!LdRqT@.dst
                #inp1!RegReadT@.src2 (getSrc2 #inp1!RegReadT@.inst);

            LET execVal <- execFn #inp1!RegReadT@.inst #bypassSrc1 #bypassSrc2
                #inp1!RegReadT@.exception;
            If #execVal!Exec@.execNextPc != #inp1!RegReadT@.nextPc
            then (
              Write pc <- #execVal!Exec@.execNextPc;
              Write execEpoch <- ! #execEpochVal;
              Retv
              );
            Enq fifoExec : Struct ExecT <-
                                  (STRUCT {
                                          wbEpoch ::= #inp1!RegReadT@.wbEpoch;
                                          instVAddr ::= #inp1!RegReadT@.instVAddr;
                                          nextPc ::= #execVal!Exec@.execNextPc;
                                          instMode ::= #inp1!RegReadT@.instMode;
                                          exception ::= #execVal!Exec@.execException;
                                          instPAddr ::= #inp1!RegReadT@.instPAddr;
                                          inst ::= #inp1!RegReadT@.inst;
                                          vAddr ::= #execVal!Exec@.execVAddr;
                                          dst ::= #execVal!Exec@.execData });
            If isLdSt #inp1!RegReadT@.inst
            then (Call memRqVToPEnq (vAddr_MemVToPRq #execVal!Exec@.execVAddr); Retv);
            Retv
            );
          Retv

        with Rule ldRq :=
          Pop inp1 : Struct ExecT <- fifoExec;
          If isLdSt #inp1!ExecT@.inst         
          then (
            Read fifoLdRqData <- fifoLdRq;
            Read fifoLdRpData <- fifoLdRp;
            Read fifoLdRqV <- fifoLdRqValid;
            Read fifoLdRpV <- fifoLdRpValid;
            LET stall <- (#fifoLdRqV && isSt #fifoLdRqData!LdRqT@.inst) ||
                (#fifoLdRpV && isSt #fifoLdRpData!LdRqT@.inst);

            Assert ! (isLd #inp1!ExecT@.inst && #stall);

            Call inp2 <- memRpVToPDeq();
            Call memRqEnq(pAddr_LdRq (memVToPRp_PAddr #inp2));
            Ret #inp2
            )
          else Ret $$ Default
          as inp2;
          Enq fifoLdRq : Struct LdRqT <- (STRUCT {
                                              wbEpoch ::= #inp1!ExecT@.wbEpoch;
                                              instVAddr ::= #inp1!ExecT@.instVAddr;
                                              nextPc ::= #inp1!ExecT@.nextPc;
                                              instMode ::= #inp1!ExecT@.instMode;
                                              exception ::= #inp1!ExecT@.exception;
                                              instPAddr ::= #inp1!ExecT@.instPAddr;
                                              inst ::= #inp1!ExecT@.inst;
                                              vAddr ::= #inp1!ExecT@.vAddr;
                                              dst ::= #inp1!ExecT@.dst;
                                              pAddr ::= memVToPRp_PAddr #inp2;
                                              dataMode ::= memVToPRp_Mode #inp2
                                         });
          Retv
          
        with Rule ldRp :=
          Pop inp1 : Struct LdRqT <- fifoLdRq;
          Enq fifoLdRp: Struct LdRqT <- #inp1;
          Retv
          
        with Rule wb :=
          Pop inp1 : Struct LdRqT <- fifoLdRp;
          Read wbEpochVal <- wbEpoch;
          Read wbPcVal <- wbPc;
          Read cStateVal <- cState;
          Read modeVal <- mode;
          LET cExecVal <- cExec #inp1!LdRqT@.inst #inp1!LdRqT@.instVAddr
              #inp1!LdRqT@.nextPc #cStateVal #inp1!LdRqT@.mode #inp1!LdRqT@.exception
              #inp1!LdRqT@.instMode #inp1!LdRqT@.dataMode;

          If isLd #inp1!LdRqT@.inst
          then (
            Call inp2 <- ldRpDeq();
            Ret #inp2
            )
          else Ret $$ Default
          as inp2;
          LET ldPAddr <- ldRp_PAddr #inp2;
          LET ldData <- ldRp_Data #inp2;

          If #wbEpochVal == #inp1!LdRqT@.wbEpoch &&
             #wbPcVal == #inp1!LdRqT@.instVAddr
          then (
            Write cState <- #cExecVal!CExec@.newCState;
            Write wbPc <- #cExecVal!CExec@.newPc;
            Write mode <- #cExecVal!CExec@.newMode;
            If #cExecVal!CExec@.newPc != #inp1!LdRqT@.nextPc
            then (
              Write wbEpoch <- ! #wbEpochVal;
              Write pc <- #cExecVal!CExec@.newPc;
              Retv
              );
            Call commitLabel (STRUCT {
                                  commitVpc ::= #inp1!LdRqT@.instVAddr;
                                  commitPc ::= #inp1!LdRqT@.instPAddr;
                                  commitInst ::= #inp1!LdRqT@.inst;
                                  commitDst ::= #inp1!LdRqT@.dst;
                                  commitVAddr ::= #inp1!LdRqT@.vAddr;
                                  commitPAddr ::= #ldPAddr;
                                  commitLdData ::= #ldData;
                                  commitMode ::= #modeVal;
                                  commitException ::= #cExecVal!CExec@.currException;
                                  commitNextPc ::= #cExecVal!CExec@.newPc;
                                  commitNextMode ::= #cExecVal!CExec@.newMode });

            If noException #cExecVal!CExec@.currException
            then (
              Call setAccessInstVToPCall(#inp1!LdRqT@.instVAddr);
              If isSt #inp1!LdRqT@.inst
              then (
                Call memRqEnq(createStRq #inp1!LdRqT@.vAddr #inp1!LdRqT@.dst);
                Call setAccessDataVToPCall(#inp1!LdRqT@.vAddr);
                Call setDirtyDataVToPCall(#inp1!LdRqT@.vAddr);
                Retv
                )
              else (
                Read regFileVals <- regFile;
                If isLd #inp1!LdRqT@.inst
                then (
                  Call setAccessDataVToPCall(#inp1!LdRqT@.vAddr);
                  Write regFile <- #regFileVals@[getDst #inp1!LdRqT@.inst <- #ldData];
                  Retv
                  )
                else (
                  Write regFile <- #regFileVals@[getDst #inp1!LdRqT@.inst <- #inp1!LdRqT@.dst];
                  Retv
                  );
                Retv
                );
              Retv
              );  
            Retv  
            );
          Retv

      }.
End Processor.

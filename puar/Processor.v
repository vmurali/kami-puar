Require Import Kami Lib.Indexer Lib.Struct Kami.Tactics Kami.SemFacts Lib.FMap
        Lib.Reflection Puar.Useful.

Set Implicit Arguments.
Set Asymmetric Patterns.

Open Scope string.
(* External method calls *)
Definition instVToPRq := "instVToPRq".
Definition instVToPRp := "instVToPRp".
Definition instRq := "instRq".
Definition instRp := "instRp".
Definition memVToPRq := "memVToPRq".
Definition memVToPRp := "memVToPRp".
Definition memRq := "memRq".
Definition memRp := "memRp".

Definition commit := "commit".
Definition setAccessInstVToP := "setAccessInstVToP".
Definition setAccessDataVToP := "setAccessDataVToP".
Definition setDirtyDataVToP := "setDirtyDataVToP".

(* Final External method calls *)
Definition getInstVToP := "getInstVToP".
Definition getInst := "getInst".
Definition getMemVToP := "getMemVToP".
Definition doMem := "doMem".

(* Field names *)
Definition nextPc := "nextPc".
Definition instMode := "instMode".
Definition exception := "exception".
Definition physicalPc := "physicalPc".
Definition inst := "inst".
Definition memVAddr := "memVAddr".
Definition src1 := "src1".
Definition src2 := "src2".
Definition dst := "dst".
Definition memPAddr := "memPAddr".
Definition memData := "memData".
Definition memMode := "memMode".
Definition byteEns := "byteEns".
Definition data := "data".
Definition op := "op".
Definition pAddr := "pAddr".
Definition instException := "instException".
Definition execException := "execException".
Definition memException := "memException".
Definition indx := "index".

(* Registers *)
Definition pc := "pc".
Definition decEpoch := "decEpoch".
Definition execEpoch := "execEpoch".
Definition wbEpoch := "wbEpoch".
Definition btb := "btb".
Definition bp := "bp".
Definition regFile := "regFile".
Definition cState := "cState".
Definition mode := "mode".
Definition wbPc := "wbPc".

Definition Valid := "Valid".

Definition fifoInstVToPRq := "fifoInstVToPRq".
Definition fifoInstVToPRqValid := "fifoInstVToPRqValid".
Definition fifoFetchRq := "fifoFetchRq".
Definition fifoFetchRqValid := "fifoFetchRqValid".
Definition fifoFetchRp := "fifoFetchRp".
Definition fifoFetchRpValid := "fifoFetchRpValid".
Definition fifoRegRead := "fifoRegRead".
Definition fifoRegReadValid := "fifoRegReadValid".

Definition fifoExec := "fifoExec".
Definition fifoExecValid := "fifoExecValid".
Definition fifoMemRq := "fifoMemRq".
Definition fifoMemRqValid := "fifoMemRqValid".
Definition fifoMemRp := "fifoMemRp".
Definition fifoMemRpValid := "fifoMemRpValid".

(* Rule names *)
Definition fetchRq := "fetchRq".
Definition fetchRp := "fetchRp".
Definition regRead := "regRead".
Definition exec := "exec".
Definition ldRq := "ldRq".
Definition ldRp := "ldRp".
Definition wb := "wb".

(* Enq (* Deq *) Pop First *)
Definition enq := "enq".
(* Definition deq := "deq". *)
Definition pop := "pop".
Definition first := "first".

(* Specification state *)
Definition stales := "stales".

(* Specification field *)
Definition staleValid := "staleValid".
Definition stalePc := "stalePc".
Definition staleInstVToPValid := "staleInstVToPValid".
Definition staleInstVToP := "staleInstVToP".
Definition staleInstValid := "staleInstValid".
Definition staleInst := "staleInst".
Definition staleMemVAddrValid := "staleMemVAddrValid".
Definition staleMemVAddr := "staleMemVAddr".
Definition staleMemVToPValid := "staleMemVAddrVToPValid".
Definition staleMemVToP := "staleMemVAddrVToP".

Definition valid := "valid".

(* Specification field *)
Definition drop := "drop".
Close Scope string.

Definition MemOp := Bit 2.

(* No exception must be 0 because I use default everywhere to denote no exception *)

Section Processor.
  Variable VAddrSz PAddrSz NumDataBytes RIndexSz: nat.
  Variable Inst CState Mode MemException ExecException FinalException: Kind.
  Definition Data := Bit (8 * NumDataBytes).
  Notation VAddr := (Bit VAddrSz).
  Definition PAddr := Bit PAddrSz.
  Variable PcInit: ConstT VAddr.
  Variable RegFileInit: ConstT (Vector Data RIndexSz).
  Variable CStateInit: ConstT CState.
  Variable ModeInit: ConstT Mode.

  Variable BtbState BpState: Kind.
  Variable BtbStateInit: ConstT BtbState.
  Variable BpStateInit: ConstT BpState.

  Notation RIndex := (Bit RIndexSz).

  Variable getSrc1: forall ty, Inst @ ty -> RIndex @ ty.
  Variable getSrc2: forall ty, Inst @ ty -> RIndex @ ty.
  Variable useSrc1: forall ty, Inst @ ty -> Bool @ ty.
  Variable useSrc2: forall ty, Inst @ ty -> Bool @ ty.
  Variable useDst: forall ty, Inst @ ty -> Bool @ ty.
  Variable getDst: forall ty, Inst @ ty -> RIndex @ ty.

  Definition Exec := STRUCT
                       { data :: Data;
                         memVAddr :: VAddr;
                         exception :: optT ExecException;
                         nextPc :: VAddr
                       }.
  
  Variable execFn: forall ty, Inst @ ty -> Data @ ty -> Data @ ty ->
                              (Struct Exec) @ ty.
  
  Definition CExec := STRUCT
                        { cState :: CState;
                          mode :: Mode;
                          exception :: optT FinalException;
                          nextPc :: VAddr
                        }.
  
  Definition VToPRp := STRUCT
                         { pAddr :: PAddr;
                           mode :: Mode;
                           exception :: optT MemException
                         }.
  
  Variable cExec:
    forall ty,
      VAddr @ ty -> PAddr @ ty -> Mode @ ty -> (optT MemException) @ ty -> Inst @ ty ->
      VAddr @ ty -> (optT ExecException) @ ty -> VAddr @ ty ->
      PAddr @ ty -> Mode @ ty -> (optT MemException) @ ty ->
      Mode @ ty -> CState @ ty -> (Struct CExec) @ ty.

  Variable isLd: forall ty, Inst @ ty -> Bool @ ty.
  Variable isSt: forall ty, Inst @ ty -> Bool @ ty.
  Variable getByteEns: forall ty, Inst @ ty -> (Bit NumDataBytes) @ ty.
  Variable isNotZero: forall ty, RIndex @ ty -> Bool @ ty.
  Variable modeLe: forall ty, Mode @ ty -> Mode @ ty -> Bool @ ty.

  Variable getNextBtb: forall ty, BtbState @ ty -> VAddr @ ty -> VAddr @ ty.
  Variable updBtb: forall ty, BtbState @ ty -> VAddr @ ty -> VAddr @ ty -> BtbState @ ty.

  Variable getBp: forall ty, BpState @ ty -> VAddr @ ty -> Inst @ ty -> VAddr @ ty.
  Variable updBp: forall ty, BtbState @ ty -> VAddr @ ty -> Inst @ ty -> Bool @ ty ->
                             BpState @ ty.

  Definition isLdSt ty (inst : Inst @ ty) := (isLd inst || isSt inst)%kami_expr.
  Notation isNm inst := (!(isLdSt inst))%kami_expr.
  
  Definition MemRq := STRUCT
                        { memPAddr :: PAddr;
                          op :: MemOp;
                          byteEns :: Bit NumDataBytes;
                          data :: Data }.

  Definition createLdRq ty (addr: PAddr @ ty): (Struct MemRq) @ ty :=
    (STRUCT { memPAddr ::= addr;
              op ::= $$ (WO~0~1);
              byteEns ::= $$ Default;
              data ::= $$ Default })%kami_expr.

  Definition createStRq ty (addr: PAddr @ ty)
             (byteEn: (Bit NumDataBytes) @ ty) (d: Data @ ty): (Struct MemRq) @ ty :=
    (STRUCT { memPAddr ::= addr;
              op ::= $$ (WO~1~0);
              byteEns ::= byteEn;
              data ::= d })%kami_expr.

  Definition InstVToPRqT := STRUCT { decEpoch :: Bool;
                                     execEpoch :: Bool;
                                     wbEpoch :: Bool;
                                     pc :: VAddr;
                                     nextPc :: VAddr
                                   }.

  Definition FetchRqT := STRUCT { decEpoch :: Bool;
                                  execEpoch :: Bool;
                                  wbEpoch :: Bool;
                                  pc :: VAddr;
                                  nextPc :: VAddr;
                                  physicalPc :: PAddr;
                                  instMode :: Mode;
                                  instException :: optT MemException
                                }.

  Definition FetchRpT := STRUCT { decEpoch :: Bool;
                                  execEpoch :: Bool;
                                  wbEpoch :: Bool;
                                  pc :: VAddr;
                                  nextPc :: VAddr;
                                  physicalPc :: PAddr;
                                  instMode :: Mode;
                                  instException :: optT MemException;
                                  inst :: Inst
                                }.

  Definition RegReadT := STRUCT { execEpoch :: Bool;
                                  wbEpoch :: Bool;
                                  pc :: VAddr;
                                  physicalPc :: PAddr;
                                  instMode :: Mode;
                                  instException :: optT MemException;
                                  inst :: Inst;
                                  src1 :: Data;
                                  src2 :: Data;
                                  nextPc :: VAddr
                                }.
  
  Definition ExecT := STRUCT { wbEpoch :: Bool;
                               pc :: VAddr;
                               physicalPc :: PAddr;
                               instMode :: Mode;
                               instException :: optT MemException;
                               inst :: Inst;
                               dst :: Data; (* Serves as data for store also *)
                               memVAddr :: VAddr;
                               execException :: optT ExecException;
                               nextPc :: VAddr
                             }.

  Definition MemRqT := STRUCT { wbEpoch :: Bool;
                                pc :: VAddr;
                                physicalPc :: PAddr;
                                instMode :: Mode;
                                instException :: optT MemException;
                                inst :: Inst;
                                dst :: Data; (* Serves as data for store also *)
                                memVAddr :: VAddr;
                                execException :: optT ExecException;
                                nextPc :: VAddr;
                                memPAddr :: PAddr;
                                memMode :: Mode;
                                memException :: optT MemException
                              }.

  Definition MemRpT := STRUCT { indx :: RIndex;
                                dst :: Data
                              }.

  Definition instVToPRqPop := MethodSig (instVToPRq -- pop) (Void): (Struct InstVToPRqT).
  Definition instVToPRqFirst := MethodSig (instVToPRq -- first) (Void): (Struct InstVToPRqT).
  Definition instVToPRpEnq := MethodSig (instVToPRp -- enq) (Struct FetchRqT): Void.
  Definition instRqPop := MethodSig (instRq -- pop) (Void): (Struct FetchRqT).
  Definition instRqFirst := MethodSig (instRq -- first) (Void): (Struct FetchRqT).
  Definition instRpEnq := MethodSig (instRp -- enq) (Struct FetchRpT): Void.

  Definition memVToPRqPop := MethodSig (memVToPRq -- pop) (Void): (Struct ExecT).
  Definition memVToPRqFirst := MethodSig (memVToPRq -- first) (Void): (Struct ExecT).
  Definition memVToPRpEnq := MethodSig (memVToPRp -- enq) (Struct MemRqT): Void.
  Definition memRqPop := MethodSig (memRq -- pop) (Void): (Struct MemRqT).
  Definition memRqFirst := MethodSig (memRq -- first) (Void): (Struct MemRqT).
  Definition memRpEnq := MethodSig (memRp -- enq) (Struct MemRpT): Void.

  Definition instVToPCall := MethodSig getInstVToP (VAddr): Struct VToPRp.
  Definition instCall := MethodSig getInst (PAddr): Inst.
  Definition memVToPCall := MethodSig getMemVToP (VAddr): Struct VToPRp.
  Definition memCall := MethodSig doMem (Struct MemRq): Data.
  Definition commitCall := MethodSig commit (VAddr): Void.

  Definition setAccessInstCall := MethodSig setAccessInstVToP (VAddr): Void.
  Definition setAccessDataCall := MethodSig setAccessDataVToP (VAddr): Void.
  Definition setDirtyDataCall := MethodSig setDirtyDataVToP (VAddr): Void.

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

  (* Notation "'Deq' f ; c" := *)
  (*   ( Read x : Bool <- (f ++ Valid)%string ; *)
  (*     Assert #x ; *)
  (*     Write (f ++ Valid)%string <- $$ false ; *)
  (*     c *)
  (*   )%kami_sin *)
  (*   (at level 12, right associativity, f at level 0) : kami_sin_scope. *)

  Notation "'First' v : kind <- f ; c" :=
    ( Read x : Bool <- (f ++ Valid)%string ;
      Assert #x ;
      Read v : kind <- f ;
      c
    )%kami_sin
    (at level 12, right associativity, f at level 0, v at level 0) : kami_sin_scope.

  Definition bypass ty (f1Valid f2Valid f3Valid: Bool @ ty)
             (f1 f2: Inst @ ty) (f3: RIndex @ ty) (f1d f2d f3d d: Data @ ty)
             (e1 e2: Bool @ ty)
             (src: RIndex @ ty) (e: Bool @ ty) :=
    ( IF (f1Valid && isNm f1 && isNotZero (getDst f1) && getDst f1 == src && useDst f1 && e1 == e)
      then f1d else
      IF (f2Valid && isNm f2 && isNotZero (getDst f2) && getDst f2 == src && useDst f2 && e2 == e)
      then f2d else
      IF (f3Valid && isNotZero f3 && f3 == src)
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

        with Register fifoFetchRp : Struct FetchRpT <- Default
        with Register fifoFetchRpValid : Bool <- (ConstBool false)
                                    
        with Register fifoRegRead : Struct RegReadT <- Default
        with Register fifoRegReadValid : Bool <- (ConstBool false)
                                    
        with Register fifoExec : Struct ExecT <- Default
        with Register fifoExecValid : Bool <- (ConstBool false)

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
          Write pc <- #nextPcVal;
          Enq fifoInstVToPRq : Struct InstVToPRqT <-
                                      (STRUCT {
                                           decEpoch ::= #decEpochVal;
                                           execEpoch ::= #execEpochVal;
                                           wbEpoch ::= #wbEpochVal;
                                           pc ::= #pcVal;
                                           nextPc ::= #nextPcVal });
          Retv

        with Rule regRead :=
          Pop inp1 : Struct FetchRpT <- fifoFetchRp;
          Read decEpochVal <- decEpoch;
          Read execEpochVal <- execEpoch;
          Read wbEpochVal <- wbEpoch;
          Read bpStateVal <- bp;
          If #decEpochVal == #inp1!FetchRpT@.decEpoch &&
             #execEpochVal == #inp1!FetchRpT@.execEpoch &&
             #wbEpochVal == #inp1!FetchRpT@.wbEpoch                               
          then (
            Read regFileVal <- regFile;
            LET instVal <- #inp1!FetchRpT@.inst;    

            Read fifoExecData <- fifoExec;
            Read fifoMemRqData <- fifoMemRq;
            Read fifoMemRpData <- fifoMemRp;
            Read fifoExecV <- fifoExecValid;
            Read fifoMemRqV <- fifoMemRqValid;
            Read fifoMemRpV <- fifoMemRpValid;

            LET stall <-
                (#fifoExecV && isLd #fifoExecData!ExecT@.inst &&
                  isNotZero (getDst #fifoExecData!ExecT@.inst) &&
                  #fifoExecData!ExecT@.wbEpoch == #wbEpochVal &&
                  ((useSrc1 #inp1!FetchRpT@.inst &&
                            getDst #fifoExecData!ExecT@.inst == getSrc1 #instVal) ||
                   (useSrc2 #inp1!FetchRpT@.inst &&
                            getDst #fifoExecData!ExecT@.inst == getSrc2 #instVal))) ||
                (#fifoMemRqV && isLd #fifoMemRqData!MemRqT@.inst &&
                  isNotZero (getDst #fifoMemRqData!MemRqT@.inst) &&
                  #fifoMemRqData!MemRqT@.wbEpoch == #wbEpochVal &&
                  ((useSrc1 #inp1!FetchRpT@.inst &&
                            getDst #fifoMemRqData!MemRqT@.inst == getSrc1 #instVal) ||
                   (useSrc2 #inp1!FetchRpT@.inst &&
                            getDst #fifoMemRqData!MemRqT@.inst == getSrc2 #instVal)));

            Assert ! #stall;

            LET bypassSrc1 <-
                bypass
                #fifoExecV #fifoMemRqV #fifoMemRpV
                #fifoExecData!ExecT@.inst #fifoMemRqData!MemRqT@.inst
                #fifoMemRpData!MemRpT@.indx
                #fifoExecData!ExecT@.dst #fifoMemRqData!MemRqT@.dst #fifoMemRpData!MemRpT@.dst
                #regFileVal@[getSrc1 #instVal]
                #fifoExecData!ExecT@.wbEpoch #fifoMemRqData!MemRqT@.wbEpoch
                (getSrc1 #inp1!FetchRpT@.inst) #wbEpochVal;

            LET bypassSrc2 <-
                bypass
                #fifoExecV #fifoMemRqV #fifoMemRpV
                #fifoExecData!ExecT@.inst #fifoMemRqData!MemRqT@.inst
                #fifoMemRpData!MemRpT@.indx
                #fifoExecData!ExecT@.dst #fifoMemRqData!MemRqT@.dst #fifoMemRpData!MemRpT@.dst
                #regFileVal@[getSrc2 #instVal]
                #fifoExecData!ExecT@.wbEpoch #fifoMemRqData!MemRqT@.wbEpoch
                (getSrc2 #inp1!FetchRpT@.inst) #wbEpochVal;



            LET nextPcVal <- getBp #bpStateVal #inp1!FetchRpT@.pc #instVal;
            If #nextPcVal != #inp1!FetchRpT@.nextPc
            then (
              Write pc <- #nextPcVal;
              Write decEpoch <- ! #decEpochVal;
              Retv
              );
            Enq fifoRegRead : Struct RegReadT <-
                                     (STRUCT {
                                          execEpoch ::= #inp1!FetchRpT@.execEpoch;
                                          wbEpoch ::= #inp1!FetchRpT@.wbEpoch;
                                          pc ::= #inp1!FetchRpT@.pc;
                                          physicalPc ::= #inp1!FetchRpT@.physicalPc;
                                          instMode ::= #inp1!FetchRpT@.instMode;
                                          instException ::= #inp1!FetchRpT@.instException;
                                          inst ::= #instVal;
                                          src1 ::= #bypassSrc1;
                                          src2 ::= #bypassSrc2;
                                          nextPc ::= #nextPcVal
                                     });
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
            LET execVal <- execFn #inp1!RegReadT@.inst #inp1!RegReadT@.src1 #inp1!RegReadT@.src2;
            
            If #execVal!Exec@.nextPc != #inp1!RegReadT@.nextPc
            then (
              Write pc <- #execVal!Exec@.nextPc;
              Write execEpoch <- ! #execEpochVal;
              Retv
              );
            Enq fifoExec : Struct ExecT <-
                                  (STRUCT {
                                          wbEpoch ::= #inp1!RegReadT@.wbEpoch;
                                          pc ::= #inp1!RegReadT@.pc;
                                          physicalPc ::= #inp1!RegReadT@.physicalPc;
                                          instMode ::= #inp1!RegReadT@.instMode;
                                          instException ::= #inp1!RegReadT@.instException;
                                          inst ::= #inp1!RegReadT@.inst;
                                          dst ::= #execVal!Exec@.data;
                                          memVAddr ::= #execVal!Exec@.memVAddr;
                                          execException ::= #execVal!Exec@.exception;
                                          nextPc ::= #execVal!Exec@.nextPc
                                  });
            Retv
            );
          Retv

        with Rule wb :=
          Pop inp1 : Struct MemRpT <- fifoMemRp;
          Read regFileVals <- regFile;
          Write regFile <- #regFileVals@[#inp1!MemRpT@.indx <- #inp1!MemRpT@.dst];
          Retv

        with Method (instVToPRq -- pop) (_: Void): (Struct InstVToPRqT) :=
          Pop inp1 : _ <- fifoInstVToPRq;
          Ret #inp1

        with Method (instRq -- pop) (_: Void): (Struct FetchRqT) :=
          Pop inp1 : _ <- fifoFetchRq;
          Ret #inp1

        with Method (memVToPRq -- pop) (_: Void): (Struct ExecT) :=
          Pop inp1 : _ <- fifoExec;
          Ret #inp1

        with Method (memRq -- pop) (_: Void): (Struct MemRqT) :=
          Pop inp1 : _ <- fifoMemRq;
          Ret #inp1

        with Method (instVToPRq -- first) (_: Void): (Struct InstVToPRqT) :=
          First inp1 : _ <- fifoInstVToPRq;
          Ret #inp1

        with Method (instRq -- first) (_: Void): (Struct FetchRqT) :=
          First inp1 : _ <- fifoFetchRq;
          Ret #inp1

        with Method (memVToPRq -- first) (_: Void): (Struct ExecT) :=
          First inp1 : _ <- fifoExec;
          Ret #inp1

        with Method (memRq -- first) (_: Void): (Struct MemRqT) :=
          First inp1 : _ <- fifoMemRq;
          Ret #inp1

        with Method (instVToPRp -- enq) (a: Struct FetchRqT): Void :=
          Enq fifoFetchRq : _ <- #a;
          Retv

        with Method (instRp -- enq) (a: Struct FetchRpT): Void :=
          Enq fifoFetchRp : _ <- #a;
          Retv

        with Method (memVToPRp -- enq) (a: Struct MemRqT): Void :=
          Enq fifoMemRq : _ <- #a;
          Retv

        with Method (memRp -- enq) (a: Struct MemRpT): Void :=
          Enq fifoMemRp : _ <- #a;
          Retv
      }.

  Definition InstVToPCall :=
    SIN {
        Rule fetchRq :=
          Call _ <- instVToPRqFirst();
          Call inp1 <- instVToPRqPop();
          Call inp2 <- instVToPCall(#inp1!InstVToPRqT@.pc);
          Call instVToPRpEnq(STRUCT {
                                 decEpoch ::= #inp1!InstVToPRqT@.decEpoch;
                                 execEpoch ::= #inp1!InstVToPRqT@.execEpoch;
                                 wbEpoch ::= #inp1!InstVToPRqT@.wbEpoch;
                                 pc ::= #inp1!InstVToPRqT@.pc;
                                 nextPc ::= #inp1!InstVToPRqT@.nextPc;
                                 physicalPc ::= #inp2!VToPRp@.pAddr;
                                 instMode ::= #inp2!VToPRp@.mode;
                                 instException ::= #inp2!VToPRp@.instException
                            });
          Retv }.
                                 
  Definition InstCall :=
    SIN {
        Rule fetchRp :=
          Call _ <- instRqFirst();
          Call inp1 <- instRqPop();
          Call inp2 <- instCall(#inp1!FetchRqT@.physicalPc);
          Call instRpEnq(STRUCT {
                             decEpoch ::= #inp1!FetchRqT@.decEpoch;
                             execEpoch ::= #inp1!FetchRqT@.execEpoch;
                             wbEpoch ::= #inp1!FetchRqT@.wbEpoch;
                             pc ::= #inp1!FetchRqT@.pc;
                             nextPc ::= #inp1!FetchRqT@.nextPc;
                             physicalPc ::= #inp1!FetchRqT@.physicalPc;
                             instMode ::= #inp1!FetchRqT@.instMode;
                             instException ::= #inp1!FetchRqT@.instException;
                             inst ::= #inp2
                        });
          Retv }.

  Definition MemVToPCall :=
    SIN {
        Rule memVToPRq :=
          Call _ <- memVToPRqFirst();
          Call inp1 <- memVToPRqPop();
          If isLdSt #inp1!ExecT@.inst         
          then (
            Call inp2 <- memVToPCall(#inp1!ExecT@.memVAddr);
            Ret #inp2
            )
          else Ret $$ Default
          as inp2;     
          Call memVToPRpEnq(STRUCT {
                                wbEpoch ::= #inp1!ExecT@.wbEpoch;
                                pc ::= #inp1!ExecT@.pc;
                                physicalPc ::= #inp1!ExecT@.physicalPc;
                                instMode ::= #inp1!ExecT@.instMode;
                                instException ::= #inp1!ExecT@.instException;
                                inst ::= #inp1!ExecT@.inst;
                                dst ::= #inp1!ExecT@.dst;
                                memVAddr ::= #inp1!ExecT@.memVAddr;
                                execException ::= #inp1!ExecT@.execException;
                                nextPc ::= #inp1!ExecT@.nextPc;
                                memPAddr ::= #inp2!VToPRp@.pAddr;
                                memMode ::= #inp2!VToPRp@.mode;
                                memException ::= #inp2!VToPRp@.exception
                           });
          Retv }.
                                 
  Definition MemCall :=
    SIN {
        Rule memRq :=
          Call _ <- memRqFirst();
          Call inp1 <- memRqPop();
          Read wbEpochVal <- wbEpoch;
          Read wbPcVal <- wbPc;
          Read cStateVal <- cState;
          Read modeVal <- mode;

          LET cExecVal <-
              cExec #inp1!MemRqT@.pc #inp1!MemRqT@.physicalPc
              #inp1!MemRqT@.instMode #inp1!MemRqT@.instException #inp1!MemRqT@.inst
              #inp1!MemRqT@.nextPc #inp1!MemRqT@.execException
              #inp1!MemRqT@.memVAddr #inp1!MemRqT@.memPAddr
              #inp1!MemRqT@.memMode #inp1!MemRqT@.memException
              #modeVal #cStateVal;

          If #wbEpochVal == #inp1!MemRqT@.wbEpoch &&
             #wbPcVal == #inp1!MemRqT@.pc
          then (
            Write cState <- #cExecVal!CExec@.cState;
            Write wbPc <- #cExecVal!CExec@.nextPc;
            Write mode <- #cExecVal!CExec@.mode;
            If #cExecVal!CExec@.nextPc != #inp1!MemRqT@.nextPc
            then (
              Write wbEpoch <- ! #wbEpochVal;
              Write pc <- #cExecVal!CExec@.nextPc;
              Retv
              );
            Call commitCall(#inp1!MemRqT@.pc);

            If ! (isSome #cExecVal!CExec@.exception)
            then (
              Call setAccessInstCall(#inp1!MemRqT@.pc);
              If isSt #inp1!MemRqT@.inst
              then (
                Call setAccessDataCall(#inp1!MemRqT@.memVAddr);
                Call setDirtyDataCall(#inp1!MemRqT@.memVAddr);                  
                Call inp2 <- memCall(createStRq #inp1!MemRqT@.memPAddr
                                                (getByteEns #inp1!MemRqT@.inst)
                                                #inp1!MemRqT@.dst);
                Ret #inp2
                )
              else (
                If isLd #inp1!MemRqT@.inst
                then (
                  Call setAccessDataCall(#inp1!MemRqT@.memVAddr);
                  Call inp2 <- memCall(createLdRq #inp1!MemRqT@.memPAddr);
                  Ret #inp2
                  )
                else Ret $$ Default
                as inp2;
                Ret #inp2
                )
              as inp2;
              LET finalDst <- IF isLd #inp1!MemRqT@.inst
                              then #inp2
                              else #inp1!MemRqT@.dst;

              Call memRpEnq(STRUCT { indx ::= getDst #inp1!MemRqT@.inst;
                                     dst ::= #finalDst
                           });
              Retv
              );  
            Retv  
            );
          Retv }.

  Notation Stale :=
    STRUCT {
        stalePc :: VAddr;
        staleInstVToP :: optT (Struct VToPRp);
        staleInst :: optT Inst;
        staleMemVAddr :: optT VAddr;
        staleMemVToP :: optT (Struct VToPRp) }.

  Notation StaleT := (Struct Stale).

  Notation Stales ty := (@NativeKind (list (ty StaleT)) nil).
  Notation Stales' := (Stales _).
  Notation addrs := (wordToNat (wones VAddrSz)).

  Open Scope kami_expr.
  Notation newStalePc val :=
    STRUCT {
        stalePc ::= val;
        staleInstVToP ::= none;
        staleInst ::= none;
        staleMemVAddr ::= none;
        staleMemVToP ::= none }.

  Notation updInstVToP s val :=
    STRUCT {
        stalePc ::= s!Stale@.stalePc;
        staleInstVToP ::= some val;
        staleInst ::= s!Stale@.staleInst;
        staleMemVAddr ::= s!Stale@.staleMemVAddr;
        staleMemVToP ::= s!Stale@.staleMemVToP }.

  Notation updInst s val :=
    STRUCT {
        stalePc ::= s!Stale@.stalePc;
        staleInstVToP ::= s!Stale@.staleInstVToP;
        staleInst ::= some val;
        staleMemVAddr ::= s!Stale@.staleMemVAddr;
        staleMemVToP ::= s!Stale@.staleMemVToP }.

  Notation updMemVAddr s val :=
    STRUCT {
        stalePc ::= s!Stale@.stalePc;
        staleInstVToP ::= s!Stale@.staleInstVToP;
        staleInst ::= s!Stale@.staleInst;
        staleMemVAddr ::= some val;
        staleMemVToP ::= s!Stale@.staleMemVToP }.

  Notation updMemVToP s val :=
    STRUCT {
        stalePc ::= s!Stale@.stalePc;
        staleInstVToP ::= s!Stale@.staleInstVToP;
        staleInst ::= s!Stale@.staleInst;
        staleMemVAddr ::= s!Stale@.staleMemVAddr;
        staleMemVToP ::= some val }.
  Close Scope kami_expr.

  Definition indexIn A i (ls: list A) :=
    match Coq.Arith.Peano_dec.eq_nat_dec i (length ls) with
    | left _ => ConstBool true
    | right _ => ConstBool false
    end.

  Definition notNil A (ls: list A) :=
    match ls with
    | nil => ConstBool false
    | _ => ConstBool true
    end.

  Definition processorSpec (n: nat) :=
    META {
        Register mode : Mode <- ModeInit
        with Register wbPc : VAddr <- PcInit
        with Register regFile : Vector Data RIndexSz <- RegFileInit
        with Register cState : CState <- CStateInit

        with RegisterN stales : Stales type <- (NativeConst nil nil)

        with Repeat Rule till addrs with VAddrSz by stalePc :=
          ILET vAddr;
          ReadN stalesVal : Stales' <- stales;
          LET newStale: StaleT <- newStalePc #vAddr;
          WriteN stales : _ <- Var _ Stales' (stalesVal ++ [newStale]);
          Retv

        with MultiRule until n as i by staleInstVToP :=
          ReadN stalesVal : Stales' <- stales;
          LET noEntry : StaleT <- $$ Default;
          LET entry : StaleT <- #(nth i stalesVal noEntry);
          LET stalePcVal : VAddr <- #entry!Stale@.stalePc;
          Assert $$ (indexIn i stalesVal);
          Call inp <- instVToPCall(#stalePcVal);
          LET newEntry: StaleT <- updInstVToP #entry #inp;
          WriteN stales : _ <- Var _ Stales' (updList newEntry i stalesVal);
          Retv

        with MultiRule until n as i by staleInst :=
          ReadN stalesVal : Stales' <- stales;
          LET noEntry : StaleT <- $$ Default;
          LET entry : StaleT <- #(nth i stalesVal noEntry);
          LET staleInstVToPVal : optT (Struct VToPRp) <- #entry!Stale@.staleInstVToP;
          Assert (isSome #staleInstVToPVal);
          Call inp <- instCall((getSome #staleInstVToPVal)!VToPRp@.pAddr);
          LET newEntry: StaleT <- updInst #entry #inp;
          WriteN stales : _ <- Var _ Stales' (updList newEntry i stalesVal);
          Retv

        with Repeat MultiRule until n as i till addrs with VAddrSz by staleMemVAddr :=
          ILET vAddr;
          ReadN stalesVal : Stales' <- stales;
          LET noEntry : StaleT <- $$ Default;
          LET entry : StaleT <- #(nth i stalesVal noEntry);
          LET staleInstVal : optT Inst <- #entry!Stale@.staleInst;
          Assert (isSome #staleInstVal);
          LET newEntry: StaleT <- updMemVAddr #entry #vAddr;
          WriteN stales : _ <- Var _ Stales' (updList newEntry i stalesVal);
          Retv

        with MultiRule until n as i by staleMemVToP :=
          ReadN stalesVal : Stales' <- stales;
          LET noEntry : StaleT <- $$ Default;
          LET entry : StaleT <- #(nth i stalesVal noEntry);
          LET staleMemVAddr : optT VAddr <- #entry!Stale@.staleMemVAddr;
          Assert (isSome #staleMemVAddr);
          Call inp <- memVToPCall(getSome #staleMemVAddr);
          LET newEntry: StaleT <- updMemVToP #entry #inp;
          WriteN stales : _ <- Var _ Stales' (updList newEntry i stalesVal);
          Retv

        with MultiRule until n as i by drop :=
          ReadN stalesVal : Stales' <- stales;
          WriteN stales : _ <- Var _ Stales' (rmList i stalesVal);
          LET noEntry : Struct Stale <- $$ Default;
          LET entry : Struct Stale <- #(hd noEntry stalesVal);
          Retv
            
        with Rule memRq :=
          ReadN stalesVal : Stales' <- stales;
          WriteN stales : _ <- Var _ Stales' (tl stalesVal);
          LET noEntry : Struct Stale <- $$ Default;
          LET inp1 : Struct Stale <- #(hd noEntry stalesVal);
          LET inst <- getSome #inp1!Stale@.staleInst;
          Read wbPcVal <- wbPc;
          Read cStateVal <- cState;
          Read regFileVals <- regFile;
          Read modeVal <- mode;

          Assert $$ (notNil stalesVal);
          Assert (isSome #inp1!Stale@.staleInstVToP);
          Assert (isSome #inp1!Stale@.staleInst);

          LET execVal <- execFn (getSome #inp1!Stale@.staleInst) #regFileVals@[getSrc1 #inst]
              #regFileVals@[getSrc2 #inst];

          If (isLdSt #inst)
          then (
            Assert (isSome #inp1!Stale@.staleMemVAddr);
            Assert (isSome #inp1!Stale@.staleMemVToP);
            Assert #execVal!Exec@.memVAddr == (getSome #inp1!Stale@.staleMemVAddr);
            Retv
            );

          LET cExecVal <-
              cExec #inp1!Stale@.stalePc
              (getSome #inp1!Stale@.staleInstVToP)!VToPRp@.pAddr
              (getSome #inp1!Stale@.staleInstVToP)!VToPRp@.mode
              (getSome #inp1!Stale@.staleInstVToP)!VToPRp@.exception
              #inst
              #execVal!Exec@.nextPc #execVal!Exec@.exception
              #execVal!Exec@.memVAddr (getSome #inp1!Stale@.staleMemVToP)!VToPRp@.pAddr
              (getSome #inp1!Stale@.staleMemVToP)!VToPRp@.mode
              (getSome #inp1!Stale@.staleMemVToP)!VToPRp@.exception
              #modeVal #cStateVal;

          If #wbPcVal == #inp1!Stale@.stalePc
          then (
            Write cState <- #cExecVal!CExec@.cState;
            Write wbPc <- #cExecVal!CExec@.pc;
            Write mode <- #cExecVal!CExec@.mode;
            Call commitCall(#inp1!Stale@.stalePc);

            If ! (isSome #cExecVal!CExec@.exception)
            then (
              Call setAccessInstCall(#inp1!Stale@.stalePc);
              If isSt #inst
              then (
                Call setAccessDataCall(getSome #inp1!Stale@.staleMemVAddr);
                Call setDirtyDataCall(getSome #inp1!Stale@.staleMemVAddr);
                Call inp2 <- memCall(createStRq
                                       (getSome #inp1!Stale@.staleMemVToP)!VToPRp@.pAddr
                                       (getByteEns #inst)
                                       #execVal!Exec@.data);
                Ret #inp2
                )
              else (
                If isLd #inst
                then (
                  Call setAccessDataCall(getSome #inp1!Stale@.staleMemVAddr);
                  Call inp2 <- memCall(createLdRq
                                         (getSome #inp1!Stale@.staleMemVToP)!VToPRp@.pAddr);
                  Ret #inp2
                  )
                else Ret $$ Default
                as inp2;
                Ret #inp2
                )
              as inp2;
              LET finalDst <- IF isLd #inst
                              then #inp2
                              else #execVal!Exec@.data;

              If (useDst #inst)
              then (
                Write regFile <- #regFileVals@[getDst #inst <- #finalDst];
                Retv
                );
              Retv
              );
            Retv
            );         
          Retv

      }.

  Section Pf.
    Notation single := (sinModuleToMetaModule 0).
    Notation proc := (single processor).
    Notation instVToPCall := (single InstVToPCall).
    Notation instCall := (single InstCall).
    Notation memVToPCall := (single MemVToPCall).
    Notation memCall := (single MemCall).

    Notation procFull := ((MetaMod proc)
                            ++++ (MetaMod instVToPCall)
                            ++++ (MetaMod instCall)
                            ++++ (MetaMod memVToPCall)
                            ++++ (MetaMod memCall)).

    Notation procFullFlattenMeta := (flattenMeta procFull).
    
    Ltac newCbv H := cbv [Valid] in H.
    
    Local Definition procFullFlat: MetaModule.
    Proof.
      pose procFullFlattenMeta as m;
        newCbv m; commonCbv m.
      simpl in m; 
        unfold Valid, Lib.VectorFacts.Vector_find in m.
      simpl in m.

      fold fifoInstVToPRqValid fifoFetchRqValid fifoFetchRpValid fifoRegReadValid
           fifoExecValid fifoMemRqValid fifoMemRpValid in m.

      finish_def.
    Defined.

    Ltac fullTrans m := ktrans m; unfold MethsT; rewrite <- idElementwiseId.


    Local Theorem procFullFlat_ref:
      (modFromMeta procFullFlattenMeta <<== modFromMeta procFullFlat) /\
      forall ty, MetaModEquiv ty typeUT procFullFlat.
    Proof.
      split; cbv [procFullFlat]; unfold MethsT;
        try rewrite idElementwiseId.
      - apply traceRefines_refl.
      - kequiv.
    Qed.

    Local Definition procFullInl': MetaModule.
    Proof.
      start_def procFullFlat.

      ssF newCbv (instVToPRq -- pop) fetchRq.
      ssF newCbv (instVToPRq -- first) fetchRq.
      ssF newCbv (instVToPRp -- enq) fetchRq.

      ssF newCbv (instRq -- pop) fetchRp.
      ssF newCbv (instRq -- first) fetchRp.
      ssF newCbv (instRp -- enq) fetchRp.

      ssF newCbv (memVToPRq -- pop) memVToPRq.
      ssF newCbv (memVToPRq -- first) memVToPRq.
      ssF newCbv (memVToPRp -- enq) memVToPRq.

      ssF newCbv (memRq -- pop) memRq.
      ssF newCbv (memRq -- first) memRq.
      ssF newCbv (memRp -- enq) memRq.

      finish_def.
    Defined.

    Definition procFullInl := ltac:(let y := eval cbv [procFullInl'] in
                                    procFullInl' in exact y).

    Local Definition procFullInl_ref':
      (modFromMeta procFullFlattenMeta <<== modFromMeta procFullInl) /\
      forall ty, MetaModEquiv ty typeUT procFullInl.
    Proof. (* SKIP_PROOF_ON
      start_ref procFullFlat procFullFlat_ref.

      ssFilt newCbv (instVToPRq -- pop) fetchRq;
      ssFilt newCbv (instVToPRq -- first) fetchRq.
      ssFilt newCbv (instVToPRp -- enq) fetchRq.

      ssFilt newCbv (instRq -- pop) fetchRp.
      ssFilt newCbv (instRq -- first) fetchRp.
      ssFilt newCbv (instRp -- enq) fetchRp.

      ssFilt newCbv (memVToPRq -- pop) memVToPRq.
      ssFilt newCbv (memVToPRq -- first) memVToPRq.
      ssFilt newCbv (memVToPRp -- enq) memVToPRq.

      ssFilt newCbv (memRq -- pop) memRq.
      ssFilt newCbv (memRq -- first) memRq.
      ssFilt newCbv (memRp -- enq) memRq.

      finish_ref.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Definition procFullInl_ref:
      (modFromMetaModules procFull <<== modFromMeta procFullInl) /\
      forall ty, MetaModEquiv ty typeUT procFullInl.
    Proof.
      destruct procFullInl_ref'.
      split; auto.
      fullTrans (modFromMeta procFullFlattenMeta); auto.
      destruct (flattenMetaEquiv procFull ltac:(noDup_tac)); assumption.
    Qed.

    Lemma processor_ModEquiv:
    MetaModPhoasWf proc.
    Proof. (* SKIP_PROOF_ON
      kequiv.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Lemma onstVToPCall_ModEquiv:
    MetaModPhoasWf instVToPCall.
    Proof. (* SKIP_PROOF_ON
      kequiv.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Lemma instCall_ModEquiv:
    MetaModPhoasWf instCall.
    Proof. (* SKIP_PROOF_ON
      kequiv.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Lemma memVToPCall_ModEquiv:
    MetaModPhoasWf memVToPCall.
    Proof. (* SKIP_PROOF_ON
      kequiv.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Lemma memCall_ModEquiv:
    MetaModPhoasWf memCall.
    Proof. (* SKIP_PROOF_ON
      kequiv.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Record VToPRpEntry := { pAddrEntry: <| PAddr |> ;
                            modeEntry: <| Mode |> ;
                            exceptEntry: <| optT MemException |>
                          }.

    Record Entry := { pcEntry: <| VAddr |> ;
                      instPEntry: option VToPRpEntry ;
                      instEntry: option <| Inst |> ;
                      memVEntry: option <| VAddr |> ;
                      memPEntry: option VToPRpEntry
                    }.

    Definition fromInstVToPRqT (s: <| Struct InstVToPRqT |>) (v: bool) :=
      (if v then
         Some {| pcEntry := s (InstVToPRqT !! pc);
                 instPEntry := None;
                 instEntry := None;
                 memVEntry := None;
                 memPEntry := None |}
       else None).
                 

    Definition fromFetchRqT (s: <| Struct FetchRqT |>) (v: bool) :=
      (if v then
         Some {| pcEntry := s (FetchRqT !! pc);
                 instPEntry := Some {|pAddrEntry := s (FetchRqT !! physicalPc);
                                      modeEntry := s (FetchRqT !! instMode);
                                      exceptEntry := s (FetchRqT !! instException)
                                    |};
                 instEntry := None;
                 memVEntry := None;
                 memPEntry := None |}
       else None).
    
    Definition fromFetchRpT (s: <| Struct FetchRpT |>) (v: bool) :=
      (if v then
         Some {| pcEntry := s (FetchRpT !! pc);
                 instPEntry := Some {|pAddrEntry := s (FetchRpT !! physicalPc);
                                      modeEntry := s (FetchRpT !! instMode);
                                      exceptEntry := s (FetchRpT !! instException)
                                    |};
                 instEntry := Some (s (FetchRpT !! inst));
                 memVEntry := None;
                 memPEntry := None |}
       else None).
    
    Definition fromRegReadT (s: <| Struct RegReadT |>) (v: bool) :=
      (if v then
         Some {| pcEntry := s (RegReadT !! pc);
                 instPEntry := Some {| pAddrEntry := s (RegReadT !! physicalPc);
                                       modeEntry := s (RegReadT !! instMode);
                                       exceptEntry := s (RegReadT !! instException)
                                    |};
                 instEntry := Some (s (RegReadT !! inst));
                 memVEntry := None;
                 memPEntry := None |}
       else None).
    
    Definition fromExecT (s: <| Struct ExecT |>) (v: bool) :=
      (if v then
         Some {| pcEntry := s (ExecT !! pc);
                 instPEntry := Some {| pAddrEntry := s (ExecT !! physicalPc);
                                       modeEntry := s (ExecT !! instMode);
                                       exceptEntry := s (ExecT !! instException)
                                    |};
                 instEntry := Some (s (ExecT !! inst));
                 memVEntry := Some (s (ExecT !! memVAddr));
                 memPEntry := None |}
       else None).
    
    Definition fromMemRqT (s: <| Struct MemRqT |>) (v: bool) :=
      (if v then
         Some {| pcEntry := s (MemRqT !! pc);
                 instPEntry := Some {| pAddrEntry := s (MemRqT !! physicalPc);
                                       modeEntry := s (MemRqT !! instMode);
                                       exceptEntry := s (MemRqT !! instException)
                                    |};
                 instEntry := Some (s (MemRqT !! inst));
                 memVEntry := Some (s (MemRqT !! memVAddr));
                 memPEntry := Some {| pAddrEntry := s (MemRqT !! memPAddr);
                                      modeEntry := s (MemRqT !! memMode);
                                      exceptEntry := s (MemRqT !! memException)
                                    |}; |}
       else None).

    Definition fromStale (s: <| Struct Stale |>) :=
      {| pcEntry := s (Stale !! stalePc);
         instPEntry :=
           if s (Stale !! staleInstVToP) ((opt (Struct VToPRp)) !! valid)
           then Some {| pAddrEntry := s (Stale !! staleInstVToP) ((opt (Struct VToPRp)) !! data)
                                        (VToPRp !! pAddr);
                        modeEntry := s (Stale !! staleInstVToP) ((opt (Struct VToPRp)) !! data)
                                       (VToPRp !! mode);
                        exceptEntry := s (Stale !! staleInstVToP) ((opt (Struct VToPRp)) !! data)
                                         (VToPRp !! exception)
                     |}
           else None;
         instEntry :=
           if s (Stale !! staleInst) ((opt Inst) !! valid)
           then Some (s (Stale !! staleInst) ((opt Inst) !! data))
           else None;
         memVEntry :=
           if s (Stale !! staleMemVAddr) ((opt VAddr) !! valid)
           then Some (s (Stale !! staleMemVAddr) ((opt VAddr) !! data))
           else None;
         memPEntry :=
           if s (Stale !! staleMemVToP) ((opt (Struct VToPRp)) !! valid)
           then Some {| pAddrEntry := s (Stale !! staleMemVToP) ((opt (Struct VToPRp)) !! data)
                                        (VToPRp !! pAddr);
                        modeEntry := s (Stale !! staleMemVToP) ((opt (Struct VToPRp)) !! data)
                                       (VToPRp !! mode);
                        exceptEntry := s (Stale !! staleMemVToP) ((opt (Struct VToPRp)) !! data)
                                         (VToPRp !! exception)
                     |}
           else None;
      |}.

    Record ExecEntry := { dataEEntry: <| Data |> ;
                          memVEEntry: <| VAddr |> ;
                          exceptEEntry: option <| ExecException |> ;
                          nextPcEEntry: <| VAddr |>
                        }.

    Definition execFromExecT (s: <| Struct ExecT |>) :=
      {| dataEEntry := s (ExecT !! dst);
         memVEEntry := s (ExecT !! memVAddr);
         exceptEEntry := if s (ExecT !! execException) ((opt ExecException) !! valid)
                         then Some (s (ExecT !! execException)
                                      ((opt ExecException) !! data))
                         else None;
         nextPcEEntry := s (ExecT !! nextPc) |}.
              
    Definition execFromMemRqT (s: <| Struct MemRqT |>) :=
      {| dataEEntry := s (MemRqT !! dst);
         memVEEntry := s (MemRqT !! memVAddr);
         exceptEEntry := if s (MemRqT !! execException) ((opt ExecException) !! valid)
                         then Some (s (MemRqT !! execException)
                                      ((opt ExecException) !! data))
                         else None;
         nextPcEEntry := s (MemRqT !! nextPc) |}.

    Definition execFromExec (s: <| Struct Exec |>) :=
      {| dataEEntry := s (Exec !! data);
         memVEEntry := s (Exec !! memVAddr);
         exceptEEntry := if s (Exec !! exception) ((opt ExecException) !! valid)
                         then Some (s (Exec !! exception) ((opt ExecException) !! data))
                         else None;
         nextPcEEntry := s (Exec !! nextPc) |}.

    Definition rfFromExecT (s: <| Struct ExecT |>) (e: bool) (rf: <| Vector Data RIndexSz |>) :=
      if bool_dec (s (ExecT !! wbEpoch)) e
      then
        if evalExpr (useDst #(s (ExecT !! inst))%kami_expr)
        then fun x => if weq x (evalExpr (getDst #(s (ExecT !! inst))%kami_expr))
                      then s (ExecT !! dst)
                      else rf x
        else rf
      else rf.

    Definition rfFromMemRqT (s: <| Struct MemRqT |>) (e: bool) (rf: <| Vector Data RIndexSz |>) :=
      if bool_dec (s (MemRqT !! wbEpoch)) e
      then
        if evalExpr (useDst #(s (MemRqT !! inst))%kami_expr)
        then fun x => if weq x (evalExpr (getDst #(s (MemRqT !! inst))%kami_expr))
                      then s (MemRqT !! dst)
                      else rf x
        else rf
      else rf.
    
    Fixpoint rmNone A (ls: list (option A)) :=
      match ls with
      | nil => nil
      | Some x :: xs => x :: rmNone xs
      | None :: xs => rmNone xs
      end.
    
    Open Scope fmap.
    Record combined_inv (i s: RegsT): Prop :=
      { modeVal: <| Mode |> ;
        modeIFind: modeVal === i.[mode] ;
        modeSFind: modeVal === s.[mode] ;

        wbPcVal: <| VAddr |> ;
        wbPcIFind: wbPcVal === i.[wbPc] ;
        wbPcSFind: wbPcVal === s.[wbPc] ;

        regFileI: <| Vector Data RIndexSz |> ;
        regFileIFind: regFileI === i.[regFile] ;
        regFileS: <| Vector Data RIndexSz |> ;
        regFileSFind: regFileS === s.[regFile] ;
        
        cStateVal: <| CState |> ;
        cStateIFind: cStateVal === i.[cState] ;
        cStateSFind: cStateVal === s.[cState] ;

        instVToPRqData: <| Struct InstVToPRqT |> ;
        instVToPRqDataFind: instVToPRqData === i.[fifoInstVToPRq] ;
        instVToPRqValid: <| Bool |> ;
        instVToPRqValidFind: instVToPRqValid === i.[fifoInstVToPRqValid] ;

        fetchRqData: <| Struct FetchRqT |> ;
        fetchRqDataFind: fetchRqData === i.[fifoFetchRq] ;
        fetchRqValid: <| Bool |> ;
        fetchRqValidFind: fetchRqValid === i.[fifoFetchRqValid] ;

        fetchRpData: <| Struct FetchRpT |> ;
        fetchRpDataFind: fetchRpData === i.[fifoFetchRp] ;
        fetchRpValid: <| Bool |> ;
        fetchRpValidFind: fetchRpValid === i.[fifoFetchRpValid] ;

        regReadData: <| Struct RegReadT |> ;
        regReadDataFind: regReadData === i.[fifoRegRead] ;
        regReadValid: <| Bool |> ;
        regReadValidFind: regReadValid === i.[fifoRegReadValid] ;

        execData: <| Struct ExecT |> ;
        execDataFind: execData === i.[fifoExec] ;
        execValid: <| Bool |> ;
        execValidFind: execValid === i.[fifoExecValid] ;

        memRqData: <| Struct MemRqT |> ;
        memRqDataFind: memRqData === i.[fifoMemRq] ;
        memRqValid: <| Bool |> ;
        memRqValidFind: memRqValid === i.[fifoMemRqValid] ;

        memRpData: <| Struct MemRpT |> ;
        memRpDataFind: memRpData === i.[fifoMemRp] ;
        memRpValid: <| Bool |> ;
        memRpValidFind: memRpValid === i.[fifoMemRpValid] ;

        staleList: <[ list (type StaleT) ]> ;
        staleListFind: staleList === s.[stales] ;

        wbEpochI: <| Bool |> ;
        wbEpochIFind: wbEpochI === i.[wbEpoch] ;

        listMatch:
          rmNone (fromInstVToPRqT instVToPRqData instVToPRqValid ::
                                  fromFetchRqT fetchRqData fetchRqValid ::
                                  fromFetchRpT fetchRpData fetchRpValid ::
                                  fromRegReadT regReadData regReadValid ::
                                  fromExecT execData execValid ::
                                  fromMemRqT memRqData memRqValid :: nil)
          = map fromStale staleList ;

        regFileMatch:
          regFileS = (fun x =>
                        if memRpValid
                        then if weq x (memRpData (MemRpT !! indx))
                             then memRpData (MemRpT !! dst)
                             else regFileI x
                        else regFileI x) ;

        regReadSrc1:
          regReadValid = true ->
          regReadData (RegReadT !! wbEpoch) = wbEpochI ->
          regReadData (RegReadT !! src1) =
          rfFromExecT execData execValid (rfFromMemRqT memRqData memRqValid regFileS)
                      (evalExpr (getSrc1 #(regReadData (RegReadT !! inst))%kami_expr)) ;

        regReadSrc2:
          regReadValid = true ->
          regReadData (RegReadT !! wbEpoch) = wbEpochI ->
          regReadData (RegReadT !! src2) =
          rfFromExecT execData execValid (rfFromMemRqT memRqData memRqValid regFileS)
                      (evalExpr (getSrc2 #(regReadData (RegReadT !! inst))%kami_expr)) ;

        execVal:
          execValid = true ->
          execData (ExecT !! wbEpoch) = wbEpochI ->
          execFromExecT execData =
          execFromExec (evalExpr
                          (execFn #(execData (ExecT !! inst))
                                  #(rfFromMemRqT memRqData memRqValid regFileS
                                                 (evalExpr (getSrc1 #(execData (ExecT !! inst)))))
                                  #(rfFromMemRqT memRqData memRqValid regFileS
                                                 (evalExpr (getSrc2 #(execData (ExecT !! inst)))))
                          )%kami_expr) ;

        memRqVal:
          memRqValid = true ->
          memRqData (MemRqT !! wbEpoch) = wbEpochI ->
          execFromMemRqT memRqData =
          execFromExec (evalExpr
                          (execFn #(memRqData (MemRqT !! inst))
                                  #(regFileS (evalExpr (getSrc1 #(memRqData (MemRqT !! inst)))))
                                  #(regFileS (evalExpr (getSrc2 #(memRqData (MemRqT !! inst)))))
                          )%kami_expr) ;

        (* TODO: Get rid of evalExpr *)
      }.
    Close Scope fmap.

    
  End Pf.
End Processor.

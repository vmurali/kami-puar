Require Import Kami Lib.Indexer Lib.Struct Kami.Tactics Kami.SemFacts Lib.Reflection Puar.Useful.

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
Definition dataMode := "dataMode".
Definition byteEns := "byteEns".
Definition data := "data".
Definition op := "op".
Definition pAddr := "pAddr".

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
  Variable Inst CState Exception Mode: Kind.
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
                       { exception :: Exception;
                         nextPc :: VAddr;
                         memVAddr :: VAddr;
                         memData :: Data }.
  
  Variable execFn: forall ty, Inst @ ty -> Data @ ty -> Data @ ty ->
                              (Struct Exec) @ ty.

  Definition CExec := STRUCT
                        { cState :: CState;
                          pc :: VAddr;
                          mode :: Mode }.
  

  Variable cExec: forall ty,  Inst @ ty -> VAddr @ ty -> VAddr @ ty -> CState @ ty ->
                              Mode @ ty -> Exception @ ty -> Mode @ ty -> Mode @ ty ->
                              (Struct CExec) @ ty.
  Variable cExecException:
    forall ty,  Inst @ ty -> VAddr @ ty -> VAddr @ ty -> CState @ ty ->
                Mode @ ty -> Mode @ ty -> Mode @ ty ->
                Exception @ ty.
  Variable isLd: forall ty, Inst @ ty -> Bool @ ty.
  Variable isSt: forall ty, Inst @ ty -> Bool @ ty.
  Variable getByteEns: forall ty, Inst @ ty -> (Bit NumDataBytes) @ ty.
  Variable isNotZero: forall ty, RIndex @ ty -> Bool @ ty.
  Variable modeLe: forall ty, Mode @ ty -> Mode @ ty -> Bool @ ty.
  Variable noException: forall ty, Exception @ ty -> Bool @ ty.

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

  Definition VToPRp := STRUCT
                         { mode :: Mode;
                           exception :: Exception;
                           pAddr :: PAddr }.
  
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
                                  instMode :: Mode;
                                  exception :: Exception;
                                  physicalPc :: PAddr
                                }.

  Definition FetchRpT := STRUCT { decEpoch :: Bool;
                                  execEpoch :: Bool;
                                  wbEpoch :: Bool;
                                  pc :: VAddr;
                                  nextPc :: VAddr;
                                  instMode :: Mode;
                                  exception :: Exception;
                                  physicalPc :: PAddr;
                                  inst :: Inst
                                }.

  Definition RegReadT := STRUCT { execEpoch :: Bool;
                                  wbEpoch :: Bool;
                                  pc :: VAddr;
                                  nextPc :: VAddr;
                                  instMode :: Mode;
                                  exception :: Exception;
                                  physicalPc :: PAddr;
                                  inst :: Inst;
                                  src1 :: Data;
                                  src2 :: Data
                                }.
  
  Definition ExecT := STRUCT { wbEpoch :: Bool;
                               pc :: VAddr;
                               nextPc :: VAddr;
                               instMode :: Mode;
                               exception :: Exception;
                               physicalPc :: PAddr;
                               inst :: Inst;
                               memVAddr :: VAddr;
                               dst :: Data (* Serves as data for store also *)
                             }.

  Definition MemRqT := STRUCT { wbEpoch :: Bool;
                                pc :: VAddr;
                                nextPc :: VAddr;
                                instMode :: Mode;
                                exception :: Exception;
                                physicalPc :: PAddr;
                                inst :: Inst;
                                memVAddr :: VAddr;
                                dst :: Data; (* Serves as data for store also *)
                                memPAddr :: PAddr;
                                dataMode :: Mode
                              }.

  Definition MemRpT := STRUCT { inst :: Inst;
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
             (f1 f2 f3: Inst @ ty) (f1d f2d f3d d: Data @ ty)
             (e1 e2: Bool @ ty)
             (src: RIndex @ ty) (e: Bool @ ty) :=
    ( IF (f1Valid && isNm f1 && isNotZero (getDst f1) && getDst f1 == src && useDst f1 && e1 == e)
      then f1d else
      IF (f2Valid && isNm f2 && isNotZero (getDst f2) && getDst f2 == src && useDst f2 && e2 == e)
      then f2d else
      IF (f3Valid && isNm f3 && isNotZero (getDst f3) && getDst f3 == src && useDst f3)
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
            LET src1Val <- #regFileVal@[getSrc1 #instVal];
            LET src2Val <- #regFileVal@[getSrc2 #instVal];
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
                                          nextPc ::= #nextPcVal;
                                          instMode ::= #inp1!FetchRpT@.instMode;
                                          exception ::= #inp1!FetchRpT@.exception;
                                          physicalPc ::= #inp1!FetchRpT@.physicalPc;
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
            Read fifoMemRqData <- fifoMemRq;
            Read fifoMemRpData <- fifoMemRp;
            Read fifoExecV <- fifoExecValid;
            Read fifoMemRqV <- fifoMemRqValid;
            Read fifoMemRpV <- fifoMemRpValid;

            LET stall <- (#fifoExecV && isLd #fifoExecData!ExecT@.inst &&
                           isNotZero (getDst #fifoExecData!ExecT@.inst) &&
                           #fifoExecData!ExecT@.wbEpoch == #inp1!RegReadT@.wbEpoch &&
                           ((useSrc1 #inp1!RegReadT@.inst &&
                                     getDst #fifoExecData!ExecT@.inst ==
                             getSrc1 #inp1!RegReadT@.inst) ||
                            (useSrc2 #inp1!RegReadT@.inst &&
                                     getDst #fifoExecData!ExecT@.inst ==
                             getSrc2 #inp1!RegReadT@.inst))) ||
                (#fifoMemRqV && isLd #fifoMemRqData!MemRqT@.inst &&
                  isNotZero (getDst #fifoMemRqData!MemRqT@.inst) &&
                  #fifoMemRqData!MemRqT@.wbEpoch == #inp1!RegReadT@.wbEpoch &&
                  ((useSrc1 #inp1!RegReadT@.inst &&
                            getDst #fifoMemRqData!MemRqT@.inst ==
                    getSrc1 #inp1!RegReadT@.inst) ||
                   (useSrc2 #inp1!RegReadT@.inst &&
                            getDst #fifoMemRqData!MemRqT@.inst ==
                    getSrc2 #inp1!RegReadT@.inst))) ||
                (#fifoMemRpV && isLd #fifoMemRpData!MemRpT@.inst &&
                  isNotZero (getDst #fifoMemRpData!MemRpT@.inst) &&
                  ((useSrc1 #inp1!RegReadT@.inst &&
                            getDst #fifoMemRpData!MemRpT@.inst ==
                    getSrc1 #inp1!RegReadT@.inst) ||
                   (useSrc2 #inp1!RegReadT@.inst &&
                            getDst #fifoMemRpData!MemRpT@.inst ==
                    getSrc1 #inp1!RegReadT@.inst)));

            Assert ! #stall;

            LET bypassSrc1 <-
                bypass
                #fifoExecV #fifoMemRqV #fifoMemRpV
                #fifoExecData!ExecT@.inst #fifoMemRqData!MemRqT@.inst #fifoMemRpData!MemRpT@.inst
                #fifoExecData!ExecT@.dst #fifoMemRqData!MemRqT@.dst #fifoMemRpData!MemRpT@.dst
                #inp1!RegReadT@.src1
                #fifoExecData!ExecT@.wbEpoch #fifoMemRqData!MemRqT@.wbEpoch
                (getSrc1 #inp1!RegReadT@.inst) #inp1!RegReadT@.wbEpoch;

            LET bypassSrc2 <-
                bypass
                #fifoExecV #fifoMemRqV #fifoMemRpV
                #fifoExecData!ExecT@.inst #fifoMemRqData!MemRqT@.inst #fifoMemRpData!MemRpT@.inst
                #fifoExecData!ExecT@.dst #fifoMemRqData!MemRqT@.dst #fifoMemRpData!MemRpT@.dst
                #inp1!RegReadT@.src2
                #fifoExecData!ExecT@.wbEpoch #fifoMemRqData!MemRqT@.wbEpoch
                (getSrc2 #inp1!RegReadT@.inst) #inp1!RegReadT@.wbEpoch;

            LET execVal <- execFn #inp1!RegReadT@.inst #bypassSrc1 #bypassSrc2;
            
            If #execVal!Exec@.nextPc != #inp1!RegReadT@.nextPc
            then (
              Write pc <- #execVal!Exec@.nextPc;
              Write execEpoch <- ! #execEpochVal;
              Retv
              );
            LET finalException <- IF noException #inp1!RegReadT@.exception
                                  then #execVal!Exec@.exception
                                  else #inp1!RegReadT@.exception;
            Enq fifoExec : Struct ExecT <-
                                  (STRUCT {
                                          wbEpoch ::= #inp1!RegReadT@.wbEpoch;
                                          pc ::= #inp1!RegReadT@.pc;
                                          nextPc ::= #execVal!Exec@.nextPc;
                                          instMode ::= #inp1!RegReadT@.instMode;
                                          exception ::= #finalException;
                                          physicalPc ::= #inp1!RegReadT@.physicalPc;
                                          inst ::= #inp1!RegReadT@.inst;
                                          memVAddr ::= #execVal!Exec@.memVAddr;
                                          dst ::= #execVal!Exec@.data });
            Retv
            );
          Retv

        with Rule wb :=
          Pop inp1 : Struct MemRpT <- fifoMemRp;
          Read regFileVals <- regFile;
          If (useDst #inp1!MemRpT@.inst)
          then (
            Write regFile <- #regFileVals@[getDst #inp1!MemRpT@.inst <- #inp1!MemRpT@.dst];
            Retv
            );
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
                                 instMode ::= #inp2!VToPRp@.mode;
                                 exception ::= #inp2!VToPRp@.exception;
                                 physicalPc ::= #inp2!VToPRp@.pAddr });
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
                             instMode ::= #inp1!FetchRqT@.instMode;
                             exception ::= #inp1!FetchRqT@.exception;
                             physicalPc ::= #inp1!FetchRqT@.pAddr;
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
          else Ret $$ Default (* The default MUST be noException *)
          as inp2;     
          LET finalException <- IF noException #inp1!ExecT@.exception
                                then #inp2!VToPRp@.exception
                                else #inp1!ExecT@.exception;
          Call memVToPRpEnq(STRUCT {
                                wbEpoch ::= #inp1!ExecT@.wbEpoch;
                                pc ::= #inp1!ExecT@.pc;
                                nextPc ::= #inp1!ExecT@.nextPc;
                                instMode ::= #inp1!ExecT@.instMode;
                                exception ::= #finalException;
                                physicalPc ::= #inp1!ExecT@.physicalPc;
                                inst ::= #inp1!ExecT@.inst;
                                memVAddr ::= #inp1!ExecT@.memVAddr;
                                dst ::= #inp1!ExecT@.dst;
                                memPAddr ::= #inp2!VToPRp@.pAddr;
                                dataMode ::= #inp2!VToPRp@.mode });
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
          LET cExecVal <- cExec #inp1!MemRqT@.inst #inp1!MemRqT@.pc
              #inp1!MemRqT@.nextPc #cStateVal #modeVal #inp1!MemRqT@.exception
              #inp1!MemRqT@.instMode #inp1!MemRqT@.dataMode;
          LET cExecExcept <- cExecException #inp1!MemRqT@.inst #inp1!MemRqT@.pc
              #inp1!MemRqT@.nextPc #cStateVal #modeVal
              #inp1!MemRqT@.instMode #inp1!MemRqT@.dataMode;

          LET finalException <- IF noException #inp1!MemRqT@.exception
                                then #cExecExcept
                                else #inp1!MemRqT@.exception;

          If #wbEpochVal == #inp1!MemRqT@.wbEpoch &&
             #wbPcVal == #inp1!MemRqT@.pc
          then (
            Write cState <- #cExecVal!CExec@.cState;
            Write wbPc <- #cExecVal!CExec@.pc;
            Write mode <- #cExecVal!CExec@.mode;
            If #cExecVal!CExec@.pc != #inp1!MemRqT@.nextPc
            then (
              Write wbEpoch <- ! #wbEpochVal;
              Write pc <- #cExecVal!CExec@.pc;
              Retv
              );
            Call commitCall(#inp1!MemRqT@.pc);

            If noException #finalException
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

              Call memRpEnq(STRUCT {
                                inst ::= #inp1!MemRqT@.inst;
                                dst ::= #finalDst
                           });
              Retv
              );  
            Retv  
            );
          Retv }.

  Notation Stale :=
    STRUCT {
        stalePc :: optionT VAddr;
        staleInstVToP :: optionT (Struct VToPRp);
        staleInst :: optionT Inst;
        staleMemVAddr :: optionT VAddr;
        staleMemVToP :: optionT (Struct VToPRp) }.

  Notation StaleT := (Struct Stale).

  Notation Stales ty := (@NativeKind (list (ty StaleT)) nil).
  Notation Stales' := (Stales _).
  Notation addrs := (wordToNat (wones VAddrSz)).

  Open Scope kami_expr.
  Notation newStalePc val :=
    STRUCT {
        stalePc ::= some val;
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
          LET stalePcVal : optionT VAddr <- #entry!Stale@.stalePc;
          Assert (isSome #stalePcVal);
          Call inp <- instVToPCall(getSome #stalePcVal);
          LET newEntry: StaleT <- updInstVToP #entry #inp;
          WriteN stales : _ <- Var _ Stales' (updList newEntry i stalesVal);
          Retv

        with MultiRule until n as i by staleInst :=
          ReadN stalesVal : Stales' <- stales;
          LET noEntry : StaleT <- $$ Default;
          LET entry : StaleT <- #(nth i stalesVal noEntry);
          LET staleInstVToPVal : optionT (Struct VToPRp) <- #entry!Stale@.staleInstVToP;
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
          LET staleInstVal : optionT Inst <- #entry!Stale@.staleInst;
          Assert (isSome #staleInstVal);
          LET newEntry: StaleT <- updMemVAddr #entry #vAddr;
          WriteN stales : _ <- Var _ Stales' (updList newEntry i stalesVal);
          Retv

        with MultiRule until n as i by staleMemVToP :=
          ReadN stalesVal : Stales' <- stales;
          LET noEntry : StaleT <- $$ Default;
          LET entry : StaleT <- #(nth i stalesVal noEntry);
          LET staleMemVAddr : optionT VAddr <- #entry!Stale@.staleMemVAddr;
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

          Assert (isSome #inp1!Stale@.stalePc);
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

                 LET execException <- IF noException
                                         (getSome #inp1!Stale@.staleInstVToP)!VToPRp@.exception
                                      then #execVal!Exec@.exception
                                      else
                                        (getSome #inp1!Stale@.staleInstVToP)!VToPRp@.exception;

          LET memVToPException <- IF noException #execException && isLdSt #inst
                                  then
                                    (getSome #inp1!Stale@.staleMemVToP)!VToPRp@.exception
                                  else #execException;

          LET cExecVal <- cExec #inst (getSome #inp1!Stale@.stalePc)
              #execVal!Exec@.nextPc #cStateVal #modeVal #memVToPException
              (getSome #inp1!Stale@.staleInstVToP)!VToPRp@.mode
              (getSome #inp1!Stale@.staleMemVToP)!VToPRp@.mode;
          LET cExecExcept <- cExecException #inst (getSome #inp1!Stale@.stalePc)
              #execVal!Exec@.nextPc #cStateVal #modeVal
              (getSome #inp1!Stale@.staleInstVToP)!VToPRp@.mode
              (getSome #inp1!Stale@.staleMemVToP)!VToPRp@.mode;

          LET finalException <- IF noException #memVToPException
                                then #cExecExcept
                                else #memVToPException;

          If #wbPcVal == getSome #inp1!Stale@.stalePc
          then (
            Write cState <- #cExecVal!CExec@.cState;
            Write wbPc <- #cExecVal!CExec@.pc;
            Write mode <- #cExecVal!CExec@.mode;
            Call commitCall(getSome #inp1!Stale@.stalePc);

            If noException #finalException
            then (
              Call setAccessInstCall(getSome #inp1!Stale@.stalePc);
              If isSt #inst
              then (
                Call setAccessDataCall(getSome #inp1!Stale@.staleMemVAddr);
                Call setDirtyDataCall(getSome #inp1!Stale@.staleMemVAddr);
                Call inp2 <- memCall(createStRq
                                       (getSome #inp1!Stale@.staleMemVToP)!VToPRp@.pAddr
                                       (getByteEns #inst)
                                       #execVal!Exec@.dst);
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
                              else #execVal!Exec@.dst;

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

  Section Multicore.
    Variable n: nat.
    Notation multiProc := (getMetaFromSinNat n processor).
    Notation multiInstVToPCall := (getMetaFromSinNat n InstVToPCall).
    Notation multiInstCall := (getMetaFromSinNat n InstCall).
    Notation multiMemVToPCall := (getMetaFromSinNat n MemVToPCall).
    Notation multiMemCall := (getMetaFromSinNat n MemCall).

    Notation multiProcFull := ((MetaMod multiProc)
                                 ++++ (MetaMod multiInstVToPCall)
                                 ++++ (MetaMod multiInstCall)
                                 ++++ (MetaMod multiMemVToPCall)
                                 ++++ (MetaMod multiMemCall)).

    Notation multiProcFullFlattenMeta := (flattenMeta multiProcFull).
    
    Ltac newCbv H := cbv [Valid] in H.
    
    Local Definition multiProcFullFlat: MetaModule.
    Proof.
      pose multiProcFullFlattenMeta as m;
        newCbv m; commonCbv m.
      simpl in m; 
        unfold Valid, Lib.VectorFacts.Vector_find in m.
      simpl in m.

      fold fifoInstVToPRqValid fifoFetchRqValid fifoFetchRpValid fifoRegReadValid
           fifoExecValid fifoMemRqValid fifoMemRpValid in m.

      finish_def.
    Defined.

    Ltac fullTrans m := ktrans m; unfold MethsT; rewrite <- idElementwiseId.


    Local Theorem multiProcFullFlat_ref:
      (modFromMeta multiProcFullFlattenMeta <<== modFromMeta multiProcFullFlat) /\
      forall ty, MetaModEquiv ty typeUT multiProcFullFlat.
    Proof.
      split; cbv [multiProcFullFlat]; unfold MethsT;
        try rewrite idElementwiseId.
      - apply traceRefines_refl.
      - kequiv.
    Qed.

    Local Definition multiProcFullInl': MetaModule.
    Proof.
      start_def multiProcFullFlat.

      ggF newCbv (instVToPRq -- pop) fetchRq.
      ggF newCbv (instVToPRq -- first) fetchRq.
      ggF newCbv (instVToPRp -- enq) fetchRq.

      ggF newCbv (instRq -- pop) fetchRp.
      ggF newCbv (instRq -- first) fetchRp.
      ggF newCbv (instRp -- enq) fetchRp.

      ggF newCbv (memVToPRq -- pop) memVToPRq.
      ggF newCbv (memVToPRq -- first) memVToPRq.
      ggF newCbv (memVToPRp -- enq) memVToPRq.

      ggF newCbv (memRq -- pop) memRq.
      ggF newCbv (memRq -- first) memRq.
      ggF newCbv (memRp -- enq) memRq.

      finish_def.
    Defined.

    Definition multiProcFullInl := ltac:(let y := eval cbv [multiProcFullInl'] in
                                         multiProcFullInl' in exact y).

    Local Definition multiProcFullInl_ref':
      (modFromMeta multiProcFullFlattenMeta <<== modFromMeta multiProcFullInl) /\
      forall ty, MetaModEquiv ty typeUT multiProcFullInl.
    Proof.
      start_ref multiProcFullFlat multiProcFullFlat_ref.

      ggFilt newCbv (instVToPRq -- pop) fetchRq;
      ggFilt newCbv (instVToPRq -- first) fetchRq.
      ggFilt newCbv (instVToPRp -- enq) fetchRq.

      ggFilt newCbv (instRq -- pop) fetchRp.
      ggFilt newCbv (instRq -- first) fetchRp.
      ggFilt newCbv (instRp -- enq) fetchRp.

      ggFilt newCbv (memVToPRq -- pop) memVToPRq.
      ggFilt newCbv (memVToPRq -- first) memVToPRq.
      ggFilt newCbv (memVToPRp -- enq) memVToPRq.

      ggFilt newCbv (memRq -- pop) memRq.
      ggFilt newCbv (memRq -- first) memRq.
      ggFilt newCbv (memRp -- enq) memRq.

      finish_ref.
    Qed.

    Definition multiProcFullInl_ref:
      (modFromMetaModules multiProcFull <<== modFromMeta multiProcFullInl) /\
      forall ty, MetaModEquiv ty typeUT multiProcFullInl.
    Proof.
      destruct multiProcFullInl_ref'.
      split; auto.
      fullTrans (modFromMeta multiProcFullFlattenMeta); auto.
      destruct (flattenMetaEquiv multiProcFull ltac:(noDup_tac)); assumption.
    Qed.

    Lemma multiProcessor_ModEquiv:
    MetaModPhoasWf multiProc.
    Proof. (* SKIP_PROOF_ON
      kequiv.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Lemma multiInstVToPCall_ModEquiv:
    MetaModPhoasWf multiInstVToPCall.
    Proof. (* SKIP_PROOF_ON
      kequiv.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Lemma multiInstCall_ModEquiv:
    MetaModPhoasWf multiInstCall.
    Proof. (* SKIP_PROOF_ON
      kequiv.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Lemma multiMemVToPCall_ModEquiv:
    MetaModPhoasWf multiMemVToPCall.
    Proof. (* SKIP_PROOF_ON
      kequiv.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Lemma multiMemCall_ModEquiv:
    MetaModPhoasWf multiMemCall.
    Proof. (* SKIP_PROOF_ON
      kequiv.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.
  End Multicore.
End Processor.

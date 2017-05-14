Require Import Kami Lib.Indexer Lib.Struct.

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
Notation fifoInstVToPRqValid := (fifoInstVToPRq ++ Valid)%string.
Definition fifoFetchRq := "fifoFetchRq".
Notation fifoFetchRqValid := (fifoFetchRq ++ Valid)%string.
Definition fifoFetchRp := "fifoFetchRp".
Notation fifoFetchRpValid := (fifoFetchRp ++ Valid)%string.
Definition fifoRegRead := "fifoRegRead".
Notation fifoRegReadValid := (fifoRegRead ++ Valid)%string.

Definition fifoExec := "fifoExec".
Notation fifoExecValid := (fifoExec ++ Valid)%string.
Definition fifoMemRq := "fifoMemRq".
Notation fifoMemRqValid := (fifoMemRq ++ Valid)%string.
Definition fifoMemRp := "fifoMemRp".
Notation fifoMemRpValid := (fifoMemRp ++ Valid)%string.

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

Close Scope string.

Definition MemOp := Bit 2.

(* No exception must be 0 because I use default everywhere to denote no exception *)

Section Processor.
  Variable VAddrSz PAddrSz NumDataBytes RIndexSz: nat.
  Variable Inst CState Exception Mode: Kind.
  Definition Data := Bit (8 * NumDataBytes).
  Definition VAddr := Bit VAddrSz.
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
  Definition isNm ty (inst : Inst @ ty) := (!(isLdSt inst))%kami_expr.
  
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
             (src: RIndex @ ty) :=
    ( IF (f1Valid && isNm f1 && isNotZero (getDst f1) && getDst f1 == src && useDst f1)
      then f1d else
      IF (f2Valid && isNm f2 && isNotZero (getDst f2) && getDst f2 == src && useDst f1)
      then f2d else
      IF (f3Valid && isNm f3 && isNotZero (getDst f3) && getDst f3 == src && useDst f1)
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

        with Register fifoMemRp : Struct MemRqT <- Default
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
                          ((useSrc1 #inp1!RegReadT@.inst &&
                            getDst #fifoExecData!ExecT@.inst == getSrc1 #inp1!RegReadT@.inst) ||
                           (useSrc2 #inp1!RegReadT@.inst &&
                            getDst #fifoExecData!ExecT@.inst == getSrc2 #inp1!RegReadT@.inst))) ||
                         (#fifoMemRqV && isLd #fifoMemRqData!MemRqT@.inst &&
                          isNotZero (getDst #fifoMemRqData!MemRqT@.inst) &&
                          ((useSrc1 #inp1!RegReadT@.inst &&
                            getDst #fifoMemRqData!MemRqT@.inst == getSrc1 #inp1!RegReadT@.inst) ||
                           (useSrc2 #inp1!RegReadT@.inst &&
                            getDst #fifoMemRqData!MemRqT@.inst == getSrc2 #inp1!RegReadT@.inst))) ||
                         (#fifoMemRpV && isLd #fifoMemRpData!MemRqT@.inst &&
                          isNotZero (getDst #fifoMemRpData!MemRqT@.inst) &&
                          ((useSrc1 #inp1!RegReadT@.inst &&
                            getDst #fifoMemRpData!MemRqT@.inst == getSrc1 #inp1!RegReadT@.inst) ||
                           (useSrc2 #inp1!RegReadT@.inst &&
                            getDst #fifoMemRpData!MemRqT@.inst == getSrc1 #inp1!RegReadT@.inst)));

            Assert ! #stall;

            LET bypassSrc1 <-
                bypass
                #fifoExecV #fifoMemRqV #fifoMemRpV
                #fifoExecData!ExecT@.inst #fifoMemRqData!MemRqT@.inst #fifoMemRpData!MemRqT@.inst
                #fifoExecData!ExecT@.dst #fifoMemRqData!MemRqT@.dst #fifoMemRpData!MemRqT@.dst
                #inp1!RegReadT@.src1 (getSrc1 #inp1!RegReadT@.inst);

            LET bypassSrc2 <-
                bypass
                #fifoExecV #fifoMemRqV #fifoMemRpV
                #fifoExecData!ExecT@.inst #fifoMemRqData!MemRqT@.inst #fifoMemRpData!MemRqT@.inst
                #fifoExecData!ExecT@.dst #fifoMemRqData!MemRqT@.dst #fifoMemRpData!MemRqT@.dst
                #inp1!RegReadT@.src2 (getSrc2 #inp1!RegReadT@.inst);

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

        with Method (memVToPRp -- enq) (a: Struct ExecT): Void :=
          Enq fifoMemRq : _ <- #a;
          Retv

        with Method (memRp -- enq) (a: Struct MemRqT): Void :=
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


End Processor.

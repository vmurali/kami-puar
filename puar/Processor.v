Require Import Kami Lib.Indexer Lib.Struct Kami.Tactics Kami.SemFacts Lib.FMap
        Lib.Reflection Puar.Useful.

Set Implicit Arguments.
Set Asymmetric Patterns.

Open Scope string.
(* External method calls *)
Notation instVToPRq := "instVToPRq".
Notation instVToPRp := "instVToPRp".
Notation instRq := "instRq".
Notation instRp := "instRp".
Notation memVToPRq := "memVToPRq".
Notation memVToPRp := "memVToPRp".
Notation memRq := "memRq".
Notation memRp := "memRp".

Notation commit := "commit".
Notation cmdInstVToP := "cmdInstVToP".
Notation cmdDataVToP := "cmdDataVToP".
Notation cmdInst := "cmdInst".
Notation cmdData := "cmdData".

(* Final External method calls *)
Notation getInstVToP := "getInstVToP".
Notation getInst := "getInst".
Notation getMemVToP := "getMemVToP".
Notation doMem := "doMem".

(* Field names *)
Notation nextPc := "nextPc".
Notation instMode := "instMode".
Notation exception := "exception".
Notation physicalPc := "physicalPc".
Notation inst := "inst".
Notation memVAddr := "memVAddr".
Notation src1 := "src1".
Notation src2 := "src2".
Notation dst := "dst".
Notation memPAddr := "memPAddr".
Notation memData := "memData".
Notation memMode := "memMode".
Notation byteEns := "byteEns".
Notation op := "op".
Notation pAddr := "pAddr".
Notation instException := "instException".
Notation execException := "execException".
Notation memException := "memException".
Notation indx := "index".

(* Registers *)
Notation pc := "pc".
Notation decEpoch := "decEpoch".
Notation execEpoch := "execEpoch".
Notation wbEpoch := "wbEpoch".
Notation btb := "btb".
Notation bp := "bp".
Notation regFile := "regFile".
Notation cState := "cState".
Notation mode := "mode".
Notation wbPc := "wbPc".

Notation Valid := "Valid".

Notation fifoInstVToPRq := "fifoInstVToPRq".
Notation fifoInstVToPRqValid := "fifoInstVToPRqValid".
Notation fifoFetchRq := "fifoFetchRq".
Notation fifoFetchRqValid := "fifoFetchRqValid".
Notation fifoFetchRp := "fifoFetchRp".
Notation fifoFetchRpValid := "fifoFetchRpValid".
Notation fifoRegRead := "fifoRegRead".
Notation fifoRegReadValid := "fifoRegReadValid".

Notation fifoExec := "fifoExec".
Notation fifoExecValid := "fifoExecValid".
Notation fifoMemRq := "fifoMemRq".
Notation fifoMemRqValid := "fifoMemRqValid".
Notation fifoMemRp := "fifoMemRp".
Notation fifoMemRpValid := "fifoMemRpValid".

(* Rule names *)
Notation fetchRq := "fetchRq".
Notation fetchRp := "fetchRp".
Notation regRead := "regRead".
Notation exec := "exec".
Notation ldRq := "ldRq".
Notation ldRp := "ldRp".
Notation wb := "wb".

(* Enq (* Deq *) Pop First *)
Notation enq := "enq".
(* Notation deq := "deq". *)
Notation pop := "pop".
Notation first := "first".

(* Specification state *)
Notation stales := "stales".

(* Specification field *)
Notation staleValid := "staleValid".
Notation stalePc := "stalePc".
Notation staleInstVToPValid := "staleInstVToPValid".
Notation staleInstVToP := "staleInstVToP".
Notation staleInstValid := "staleInstValid".
Notation staleInst := "staleInst".
Notation staleMemVAddrValid := "staleMemVAddrValid".
Notation staleMemVAddr := "staleMemVAddr".
Notation staleMemVToPValid := "staleMemVAddrVToPValid".
Notation staleMemVToP := "staleMemVAddrVToP".
Notation drop := "drop".
Close Scope string.

Definition MemOp := Bit 2.

(* No exception must be 0 because I use default everywhere to denote no exception *)

Section Processor.
  Variable VAddrSz PAddrSz NumDataBytes RIndexSz: nat.
  Variable Inst MemRq CState Mode MemException ExecException FinalException
    CmdInstVToP CmdDataVToP CmdInst CmdData: Kind.
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

  Variable getSrc1: forall ty, ty Inst -> RIndex @ ty.
  Variable getSrc2: forall ty, ty Inst -> RIndex @ ty.
  Variable useSrc1: forall ty, ty Inst -> Bool @ ty.
  Variable useSrc2: forall ty, ty Inst -> Bool @ ty.
  Variable useDst: forall ty, ty Inst -> Bool @ ty.
  Variable getDst: forall ty, ty Inst -> RIndex @ ty.

  Definition Exec := STRUCT
                       { data :: Data;
                         memVAddr :: VAddr;
                         exception :: optT ExecException;
                         nextPc :: VAddr
                       }.
  
  Variable execFn: forall ty, ty Inst -> ty Data -> ty Data ->
                              (Struct Exec) @ ty.
  
  Definition CExec := STRUCT
                        { cState :: CState;
                          mode :: Mode;
                          exception :: optT FinalException;
                          nextPc :: VAddr;
                          cmdInstVToP :: CmdInstVToP;
                          cmdDataVToP :: CmdDataVToP;
                          cmdInst :: CmdInst;
                          cmdData :: CmdData
                        }.
  
  Definition VToPRp := STRUCT
                         { pAddr :: PAddr;
                           mode :: Mode;
                           exception :: optT MemException
                         }.
  
  Variable cExec:
    forall ty,
      ty VAddr -> ty PAddr -> ty Mode -> ty (optT MemException) -> ty Inst ->
      ty VAddr -> ty (optT ExecException) -> ty VAddr ->
      ty PAddr -> ty Mode -> ty (optT MemException) ->
      ty Mode -> ty CState -> (Struct CExec) @ ty.

  Variable isLd: forall ty, ty Inst -> Bool @ ty.
  Variable isSt: forall ty, ty Inst -> Bool @ ty.
  Variable isNotZero: forall ty, ty RIndex -> Bool @ ty.

  Variable getNextBtb: forall ty, ty BtbState -> ty VAddr -> VAddr @ ty.
  Variable updBtb: forall ty, ty BtbState -> ty VAddr -> ty VAddr -> BtbState @ ty.

  Variable getBp: forall ty, ty BpState -> ty VAddr -> ty Inst -> VAddr @ ty.
  Variable updBp: forall ty, ty BtbState -> ty VAddr -> ty Inst -> ty Bool ->
                             BpState @ ty.

  Notation isLdSt ty inst := (isLd ty inst || isSt ty inst)%kami_expr.
  Notation isNm ty inst := (!(isLdSt ty inst))%kami_expr.


  Variable createMemRq: forall ty, ty Inst -> ty PAddr -> ty Data -> MemRq @ ty.

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
  Definition memCall := MethodSig doMem (MemRq): Data.
  Definition commitCall := MethodSig commit (VAddr): Void.

  Definition cmdInstVToPCall := MethodSig cmdInstVToP (CmdInstVToP): Void.
  Definition cmdDataVToPCall := MethodSig cmdDataVToP (CmdDataVToP): Void.
  Definition cmdInstCall := MethodSig cmdInst (CmdInst): Void.
  Definition cmdDataCall := MethodSig cmdData (CmdData): Void.

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

  Definition bypass ty (f1Valid f2Valid f3Valid: ty Bool)
             (nm1 nm2: ty Bool)
             (dst1 dst2 dst3 src: ty RIndex)
             (nz1 nz2 nz3: ty Bool)
             (ud1 ud2: ty Bool)
             (f1d f2d f3d d: ty Data)
             (e1 e2 e: ty Bool) :=
    ( IF (#f1Valid && #nm1 && #nz1 && #dst1 == #src && #ud1 && #e1 == #e)
      then #f1d else
      IF (#f2Valid && #nm2 && #nz2 && #dst2 == #src && #ud2 && #e2 == #e)
      then #f2d else
      IF (#f3Valid && #nz3 && #dst3 == #src)
      then #f3d else #d
    )%kami_expr.
  
  (* Definition bypass ty (f1Valid f2Valid f3Valid: Bool @ ty) *)
  (*            (f1 f2: Inst @ ty) (f3: RIndex @ ty) (f1d f2d f3d d: Data @ ty) *)
  (*            (e1 e2: Bool @ ty) *)
  (*            (src: RIndex @ ty) (e: Bool @ ty) := *)
  (*   ( IF (f1Valid && isNm f1 && isNotZero (getDst f1) && getDst f1 == src && useDst f1 && e1 == e) *)
  (*     then f1d else *)
  (*     IF (f2Valid && isNm f2 && isNotZero (getDst f2) && getDst f2 == src && useDst f2 && e2 == e) *)
  (*     then f2d else *)
  (*     IF (f3Valid && isNotZero f3 && f3 == src) *)
  (*     then f3d else d *)
  (*   )%kami_expr. *)
  
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
          Read btbStateVal: BtbState <- btb;
          LET nextPcVal <- getNextBtb _ btbStateVal pcVal;
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
          LET instVal <- #inp1!FetchRpT@.inst;
          LET pcVal <- #inp1!FetchRpT@.pc;
          Read decEpochVal <- decEpoch;
          Read execEpochVal <- execEpoch;
          Read wbEpochVal <- wbEpoch;
          Read bpStateVal: BpState <- bp;
          If #decEpochVal == #inp1!FetchRpT@.decEpoch &&
             #execEpochVal == #inp1!FetchRpT@.execEpoch &&
             #wbEpochVal == #inp1!FetchRpT@.wbEpoch                               
          then (
            Read regFileVal <- regFile;

            Read fifoExecV <- fifoExecValid;
            Read fifoMemRqV <- fifoMemRqValid;
            Read fifoMemRpV: Bool <- fifoMemRpValid;

            Read fifoExecData <- fifoExec;
            Read fifoMemRqData <- fifoMemRq;
            Read fifoMemRpData <- fifoMemRp;

            LET execInst <- #fifoExecData!ExecT@.inst;
            LET memRqInst <- #fifoMemRqData!MemRqT@.inst;
            LET memRpInst <- #fifoMemRpData!MemRpT@.inst;
            
            LET execNm <- isNm _ execInst;
            LET memRqNm <- isNm _ memRqInst;

            LET execLd <- isLd _ execInst;
            LET memRqLd <- isLd _ memRqInst;

            LET execDst <- getDst _ execInst;
            LET memRqDst <- getDst _ memRqInst;
            LET memRpDst <- #fifoMemRpData!MemRpT@.indx;

            LET execNz <- isNotZero _ execDst;
            LET memRqNz <- isNotZero _ memRqDst;
            LET memRpNz <- isNotZero _ memRpDst;

            LET execUse <- useDst _ execInst;
            LET memRqUse <- useDst _ memRqInst;

            LET src1Val <- getSrc1 _ instVal;
            LET src2Val <- getSrc2 _ instVal;

            LET use1 <- useSrc1 _ instVal;
            LET use2 <- useSrc2 _ instVal;

            LET execData <- #fifoExecData!ExecT@.dst;
            LET memRqData <- #fifoMemRqData!MemRqT@.dst;
            LET memRpData <- #fifoMemRpData!MemRpT@.dst;

            LET src1Data <- #regFileVal@[#src1Val];
            LET src2Data <- #regFileVal@[#src2Val];

            LET execWbEpoch <- #fifoExecData!ExecT@.wbEpoch;
            LET memRqWbEpoch <- #fifoMemRqData!MemRqT@.wbEpoch;

            LET stall <-
                (#fifoExecV && #execLd && #execUse && #execNz &&
                  #execWbEpoch == #wbEpochVal &&
                  ((#use1 && #execDst == #src1Val) || (#use2 && #execDst == #src2Val))) ||
                (#fifoMemRqV && #memRqLd && #memRqUse && #memRqNz &&
                  #memRqWbEpoch == #wbEpochVal &&
                  ((#use1 && #memRqDst == #src1Val) || (#use2 && #memRqDst == #src2Val)));

            Assert ! #stall;

            LET bypassSrc1 <-
                bypass _
                fifoExecV fifoMemRqV fifoMemRpV
                execNm memRqNm
                execDst memRqDst memRpDst src1Val
                execNz memRqNz memRpNz
                execUse memRqUse
                execData memRqData memRpData src1Data
                execWbEpoch memRqWbEpoch wbEpochVal;

            LET bypassSrc2 <-
                bypass _
                fifoExecV fifoMemRqV fifoMemRpV
                execNm memRqNm
                execDst memRqDst memRpDst src2Val
                execNz memRqNz memRpNz
                execUse memRqUse
                execData memRqData memRpData src2Data
                execWbEpoch memRqWbEpoch wbEpochVal;

            LET nextPcVal <- getBp _ bpStateVal pcVal instVal;
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
          LET instVal <- #inp1!RegReadT@.inst;
          LET src1Val <- #inp1!RegReadT@.src1;
          LET src2Val <- #inp1!RegReadT@.src2;
          Read execEpochVal <- execEpoch;
          Read wbEpochVal <- wbEpoch;
          If #execEpochVal == #inp1!RegReadT@.execEpoch &&
             #wbEpochVal == #inp1!RegReadT@.wbEpoch                               
          then (
            LET execVal <- execFn _ instVal src1Val src2Val;
            
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
          LET instVal <- #inp1!ExecT@.inst;
          If isLdSt _ instVal   
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
          Read cStateVal: CState <- cState;
          Read modeVal: Mode <- mode;

          LET pcVal <- #inp1!MemRqT@.pc;
          LET physicalPcVal <- #inp1!MemRqT@.physicalPc;
          LET instModeVal <- #inp1!MemRqT@.instMode;
          LET instExceptionVal <- #inp1!MemRqT@.instException;
          LET instVal <- #inp1!MemRqT@.inst;
          LET nextPcVal <- #inp1!MemRqT@.nextPc;
          LET execExceptionVal <- #inp1!MemRqT@.execException;
          LET memVAddrVal <- #inp1!MemRqT@.memVAddr;
          LET memPAddrVal <- #inp1!MemRqT@.memPAddr;
          LET memModeVal <- #inp1!MemRqT@.memMode;
          LET memExceptionVal <- #inp1!MemRqT@.memException;
          LET dstVal <- #inp1!MemRqT@.dst;

          LET cExecVal <- cExec _ pcVal physicalPcVal instModeVal instExceptionVal
              instVal nextPcVal execExceptionVal memVAddrVal memPAddrVal memModeVal
              memExceptionVal modeVal cStateVal;

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
              Call cmdInstVToPCall(#cExecVal!CExec@.cmdInstVToP);
              Call cmdDataVToPCall(#cExecVal!CExec@.cmdDataVToP);
              Call cmdInstCall(#cExecVal!CExec@.cmdInst);
              Call cmdDataCall(#cExecVal!CExec@.cmdData);
                  
              If isLdSt _ instVal
              then (
                Call inp2 <- memCall(createMemRq _ instVal memPAddrVal dstVal);
                Ret #inp2
                )
              else (
                Ret $$ Default
                )
              as inp2;
              LET finalDst <- IF isLd _ instVal
                              then #inp2
                              else #inp1!MemRqT@.dst;

              If (useDst _ instVal)
              then (Call memRpEnq(STRUCT { indx ::= getDst _ instVal;
                                           dst ::= #finalDst
                                 }); Retv);
              Retv
              );  
            Retv  
            );
          Retv }.

  Record VToPRpEntry {ty} := { pAddrEntry: ty PAddr ;
                               modeEntry: ty Mode ;
                               exceptEntry: option (ty MemException)
                             }.

  Record Stale ty := { sPc: ty VAddr ;
                       sInstVToP: option (@VToPRpEntry ty) ;
                       sInst: option (ty Inst) ;
                       sMemVAddr: option (ty VAddr) ;
                       sMemVToP: option (@VToPRpEntry ty)
                     }.

  Definition newStalePc {ty} (val: ty VAddr) := {| sPc := val;
                                                   sInstVToP := None;
                                                   sInst := None;
                                                   sMemVAddr := None;
                                                   sMemVToP := None |}.

  Definition updInstVToP {ty} (s: Stale ty) val :=
    {| sPc := sPc s;
       sInstVToP := Some val;
       sInst := sInst s;
       sMemVAddr := sMemVAddr s;
       sMemVToP := sMemVToP s |}.

  Definition updInst {ty} (s: Stale ty) val :=
    {| sPc := sPc s;
       sInstVToP := sInstVToP s;
       sInst := Some val;
       sMemVAddr := sMemVAddr s;
       sMemVToP := sMemVToP s |}.

  Definition updMemVAddr {ty} (s: Stale ty) val :=
    {| sPc := sPc s;
       sInstVToP := sInstVToP s;
       sInst := sInst s;
       sMemVAddr := Some val;
       sMemVToP := sMemVToP s |}.

  Definition updMemVToP {ty} (s: Stale ty) val :=
    {| sPc := sPc s;
       sInstVToP := sInstVToP s;
       sInst := sInst s;
       sMemVAddr := sMemVAddr s;
       sMemVToP := Some val |}.

  Notation StaleT ty val := (@NativeKind (Stale ty) (newStalePc val)).
  Notation StaleT' val := (StaleT _ val).
  Notation Stales ty := (@NativeKind (list (Stale ty)) nil).
  Notation Stales' := (Stales _).

  Notation NativeVar ntype nval := (Var _ (@NativeKind ntype nval) nval).

  Definition processorSpec :=
    SIN {
        Register mode : Mode <- ModeInit
        with Register wbPc : VAddr <- PcInit
        with Register regFile : Vector Data RIndexSz <- RegFileInit
        with Register cState : CState <- CStateInit

        with RegisterN stales : Stales type <- (NativeConst nil nil)

        with Rule stalePc :=
          ReadN stalesVal : Stales' <- stales;
          Nondet vAddr: SyntaxKind VAddr;
          WriteN stales : _ <- Var _ Stales' (stalesVal ++ [newStalePc vAddr]);
          Retv

        with Rule staleInstVToP :=
          ReadN stalesVal : Stales' <- stales;
          Nondet i: @NativeKind nat 0;
          Assert $$ (indexIn i stalesVal);
          LET vAddrDef : VAddr <- $$ Default;
          Call inp <- instVToPCall(#(sPc (nth i stalesVal (newStalePc vAddrDef))));
          LET p <- #inp!VToPRp@.pAddr;
          LET m <- #inp!VToPRp@.mode;
          LET e <- getSome #inp!VToPRp@.exception;
          LETN e': _ <- IF isSome #inp!VToPRp@.exception == $$ true
                        then Var _ (@NativeKind (option (_ MemException)) None) (Some e)
                        else Var _ (@NativeKind (option (_ MemException)) None) None;
          WriteN stales : _ <- Var _ Stales' (nth_upd updInstVToP {| pAddrEntry := p;
                                                                     modeEntry := m;
                                                                     exceptEntry := e' |}
                                                      i stalesVal);
          Retv

        with Rule staleInst :=
          ReadN stalesVal : Stales' <- stales;
          Nondet i: @NativeKind nat 0;
          Assert $$ (indexIn i stalesVal);
          LET vAddrDef : VAddr <- $$ Default;
          LET pAddrDef : PAddr <- $$ Default;
          LET modeDef : Mode <- $$ Default;
          LETN vToPRpDef : _ <- NativeVar VToPRpEntry {| pAddrEntry := pAddrDef;
                                                         modeEntry := modeDef;
                                                         exceptEntry := None |};
          Call inp <- instCall(#(pAddrEntry
                                   (rmSome
                                      vToPRpDef
                                      (sInstVToP
                                         (nth i stalesVal (newStalePc vAddrDef))))));
          WriteN stales : _ <- Var _ Stales' (nth_upd updInst inp i stalesVal);
          Retv

        with Rule staleMemVAddr :=
          ReadN stalesVal : Stales' <- stales;
          Nondet i: @NativeKind nat 0;
          Assert $$ (indexIn i stalesVal);
          Nondet vAddr: SyntaxKind VAddr;
          WriteN stales : _ <- Var _ Stales' (nth_upd updMemVAddr vAddr i stalesVal);
          Retv

        with Rule staleMemVToP :=
          ReadN stalesVal : Stales' <- stales;
          Nondet i: @NativeKind nat 0;
          Assert $$ (indexIn i stalesVal);
          LET vAddrDef : VAddr <- $$ Default;
          Call inp <- memVToPCall(#(sPc (nth i stalesVal (newStalePc vAddrDef))));
          LET p <- #inp!VToPRp@.pAddr;
          LET m <- #inp!VToPRp@.mode;
          LET e <- getSome #inp!VToPRp@.exception;
          LETN e': _ <- IF isSome #inp!VToPRp@.exception == $$ true
                        then Var _ (@NativeKind (option (_ MemException)) None) (Some e)
                        else Var _ (@NativeKind (option (_ MemException)) None) None;
          WriteN stales : _ <- Var _ Stales' (nth_upd updMemVToP {| pAddrEntry := p;
                                                                    modeEntry := m;
                                                                    exceptEntry := e' |}
                                                      i stalesVal);
          Retv
            
        with Rule memRq :=
          ReadN stalesVal : Stales' <- stales;

          Read wbPcVal: VAddr <- wbPc;
          Read cStateVal: CState <- cState;
          Read regFileVals: Vector Data RIndexSz <- regFile;
          Read modeVal: Mode <- mode;

          LET vAddrDef : VAddr <- $$ Default;
          LETN inp1 : _ <- Var _ (StaleT' vAddrDef) (hd (newStalePc vAddrDef) stalesVal);
          LET pAddrDef: PAddr <- $$ Default;
          LET modeDef: Mode <- $$ Default;
          LETN vToPRpDef: _ <- NativeVar VToPRpEntry {| pAddrEntry := pAddrDef;
                                                        modeEntry := modeDef;
                                                        exceptEntry := None |} ;
          LET memExceptDef: MemException <- $$ Default ;
          LET instDef: Inst <- $$ Default;

          LET pcVal <- #(sPc inp1);
          LET physicalPcVal <- #(pAddrEntry (rmSome vToPRpDef (sInstVToP inp1)));
          LET instModeVal <- #(modeEntry (rmSome vToPRpDef (sInstVToP inp1)));
          LET instExceptionVal <-
              STRUCT {
                valid ::= $$ (isValid (exceptEntry (rmSome vToPRpDef (sInstVToP inp1))));
                data ::= #(rmSome memExceptDef
                                  (exceptEntry (rmSome vToPRpDef (sInstVToP inp1)))) };
          LET instVal <- #(rmSome instDef (sInst inp1));
          LET memVAddrVal1 <- #(rmSome vAddrDef (sMemVAddr inp1));
          LET memPAddrVal <- #(pAddrEntry (rmSome vToPRpDef (sMemVToP inp1)));
          LET memModeVal <- #(modeEntry (rmSome vToPRpDef (sMemVToP inp1)));
          LET memExceptionVal <-
              STRUCT {
                valid ::= $$ (isValid (exceptEntry (rmSome vToPRpDef (sMemVToP inp1))));
                data ::= #(rmSome memExceptDef
                                  (exceptEntry (rmSome vToPRpDef (sMemVToP inp1)))) };

          LET src1Val <- #regFileVals@[getSrc1 _ instVal];
          LET src2Val <- #regFileVals@[getSrc2 _ instVal];

          LET execVal <- execFn _ instVal src1Val src2Val;

          LET nextPcVal <- #execVal!Exec@.nextPc;
          LET execExceptionVal <- #execVal!Exec@.exception;
          LET memVAddrVal <- #execVal!Exec@.memVAddr;
          LET dstVal <- #execVal!Exec@.data;

            
          Assert $$ (notNil stalesVal);
          Assert $$ (isValid (sInstVToP inp1));
          Assert $$ (isValid (sInst inp1));

          If (isLdSt _ instVal)
          then (
            Assert $$ (isValid (sMemVAddr inp1));
            Assert $$ (isValid (sMemVToP inp1));
            Assert #memVAddrVal == #memVAddrVal1;
            Retv
            );

          LET cExecVal <- cExec _ pcVal physicalPcVal instModeVal instExceptionVal
              instVal nextPcVal execExceptionVal memVAddrVal memPAddrVal memModeVal
              memExceptionVal modeVal cStateVal;

          If #wbPcVal == #pcVal
          then (
            Write cState <- #cExecVal!CExec@.cState;
            Write wbPc <- #cExecVal!CExec@.nextPc;
            Write mode <- #cExecVal!CExec@.mode;
            Call commitCall(#pcVal);

            If ! (isSome #cExecVal!CExec@.exception)
            then (
              Call cmdInstVToPCall(#cExecVal!CExec@.cmdInstVToP);
              Call cmdDataVToPCall(#cExecVal!CExec@.cmdDataVToP);
              Call cmdInstCall(#cExecVal!CExec@.cmdInst);
              Call cmdDataCall(#cExecVal!CExec@.cmdData);
                  
              If isLdSt _ instVal
              then (
                Call inp2 <- memCall(createMemRq _ instVal memPAddrVal dstVal);
                Ret #inp2
                )
              else (
                Ret $$ Default
                )
              as inp2;
              LET finalDst <- IF isLd _ instVal
                              then #inp2
                              else #dstVal;

              If (useDst _ instVal)
              then (
                Write regFile <- #regFileVals@[getDst _ instVal <- #finalDst];
                Retv
                );
              Retv
              );
            Retv
            );

          WriteN stales : _ <- Var _ Stales' (tl stalesVal);
          Retv
      }.

  Section Pf.
    Variable n: nat.
    Notation single := (sinModuleToMetaModule n).
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
    
    Ltac newCbv H := idtac.
    
    Local Definition procFullFlat: MetaModule.
    Proof.
      pose procFullFlattenMeta as m;
        newCbv m; commonCbv m.
      simpl in m; 
        unfold Lib.VectorFacts.Vector_find in m.
      simpl in m.

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

      ssF newCbv (instVToPRq -- pop) (fetchRq).
      ssF newCbv (instVToPRq -- first) (fetchRq).
      ssF newCbv (instVToPRp -- enq) (fetchRq).

      ssF newCbv (instRq -- pop) (fetchRp).
      ssF newCbv (instRq -- first) (fetchRp).
      ssF newCbv (instRp -- enq) (fetchRp).

      ssF newCbv (memVToPRq -- pop) (memVToPRq).
      ssF newCbv (memVToPRq -- first) (memVToPRq).
      ssF newCbv (memVToPRp -- enq) (memVToPRq).

      ssF newCbv (memRq -- pop) (memRq).
      ssF newCbv (memRq -- first) (memRq).
      ssF newCbv (memRp -- enq) (memRq).

      finish_def.
    Defined.

    Definition procFullInl := ltac:(let y := eval cbv [procFullInl'] in
                                    procFullInl' in exact y).

    Notation procFullInlM := (modFromMeta procFullInl).
    Local Definition procFullInl_ref':
      (modFromMeta procFullFlattenMeta <<== procFullInlM) /\
      forall ty, MetaModEquiv ty typeUT procFullInl.
    Proof. (* SKIP_PROOF_ON
      start_ref procFullFlat procFullFlat_ref.

      ssFilt newCbv (instVToPRq -- pop) (fetchRq);
      ssFilt newCbv (instVToPRq -- first) (fetchRq).
      ssFilt newCbv (instVToPRp -- enq) (fetchRq).

      ssFilt newCbv (instRq -- pop) (fetchRp).
      ssFilt newCbv (instRq -- first) (fetchRp).
      ssFilt newCbv (instRp -- enq) (fetchRp).

      ssFilt newCbv (memVToPRq -- pop) (memVToPRq).
      ssFilt newCbv (memVToPRq -- first) (memVToPRq).
      ssFilt newCbv (memVToPRp -- enq) (memVToPRq).

      ssFilt newCbv (memRq -- pop) (memRq).
      ssFilt newCbv (memRq -- first) (memRq).
      ssFilt newCbv (memRp -- enq) (memRq).

      finish_ref.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Definition procFullInl_ref:
      (modFromMetaModules procFull <<== procFullInlM) /\
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

    Definition fromInstVToPRqT (s: <| Struct InstVToPRqT |>) (v: bool) :=
      (if v then
         Some {| sPc := s (InstVToPRqT !! pc);
                 sInstVToP := None;
                 sInst := None;
                 sMemVAddr := None;
                 sMemVToP := None |}
       else None).
                 
    Definition fromFetchRqT (s: <| Struct FetchRqT |>) (v: bool) :=
      (if v then
         Some {| sPc := s (FetchRqT !! pc);
                 sInstVToP := Some {|pAddrEntry := s (FetchRqT !! physicalPc);
                                     modeEntry := s (FetchRqT !! instMode);
                                     exceptEntry :=
                                       if s (FetchRqT !! instException)
                                            ((opt MemException) !! valid)
                                       then Some (s (FetchRqT !! instException)
                                                    ((opt MemException) !! data))
                                       else None
                                   |};
                 sInst := None;
                 sMemVAddr := None;
                 sMemVToP := None |}
       else None).
    
    Definition fromFetchRpT (s: <| Struct FetchRpT |>) (v: bool) :=
      (if v then
         Some {| sPc := s (FetchRpT !! pc);
                 sInstVToP := Some {|pAddrEntry := s (FetchRpT !! physicalPc);
                                     modeEntry := s (FetchRpT !! instMode);
                                     exceptEntry :=
                                       if s (FetchRpT !! instException)
                                            ((opt MemException) !! valid)
                                       then Some (s (FetchRpT !! instException)
                                                    ((opt MemException) !! data))
                                       else None
                                   |};
                 sInst := Some (s (FetchRpT !! inst));
                 sMemVAddr := None;
                 sMemVToP := None |}
       else None).
    
    Definition fromRegReadT (s: <| Struct RegReadT |>) (v: bool) :=
      (if v then
         Some {| sPc := s (RegReadT !! pc);
                 sInstVToP := Some {|pAddrEntry := s (RegReadT !! physicalPc);
                                     modeEntry := s (RegReadT !! instMode);
                                     exceptEntry :=
                                       if s (RegReadT !! instException)
                                            ((opt MemException) !! valid)
                                       then Some (s (RegReadT !! instException)
                                                    ((opt MemException) !! data))
                                       else None
                                   |};
                 sInst := Some (s (RegReadT !! inst));
                 sMemVAddr := None;
                 sMemVToP := None |}
       else None).
    
    Definition fromExecT (s: <| Struct ExecT |>) (v: bool) :=
      (if v then
         Some {| sPc := s (ExecT !! pc);
                 sInstVToP := Some {|pAddrEntry := s (ExecT !! physicalPc);
                                     modeEntry := s (ExecT !! instMode);
                                     exceptEntry :=
                                       if s (ExecT !! instException)
                                            ((opt MemException) !! valid)
                                       then Some (s (ExecT !! instException)
                                                    ((opt MemException) !! data))
                                       else None
                                   |};
                 sInst := Some (s (ExecT !! inst));
                 sMemVAddr := Some (s (ExecT !! memVAddr));
                 sMemVToP := None |}
       else None).
    
    Definition fromMemRqT (s: <| Struct MemRqT |>) (v: bool) :=
      (if v then
         Some {| sPc := s (MemRqT !! pc);
                 sInstVToP := Some {|pAddrEntry := s (MemRqT !! physicalPc);
                                     modeEntry := s (MemRqT !! instMode);
                                     exceptEntry :=
                                       if s (MemRqT !! instException)
                                            ((opt MemException) !! valid)
                                       then Some (s (MemRqT !! instException)
                                                    ((opt MemException) !! data))
                                       else None
                                   |};
                 sInst := Some (s (MemRqT !! inst));
                 sMemVAddr := Some (s (MemRqT !! memVAddr));
                 sMemVToP := Some {|pAddrEntry := s (MemRqT !! memPAddr);
                                    modeEntry := s (MemRqT !! memMode);
                                    exceptEntry :=
                                      if s (MemRqT !! memException)
                                           ((opt MemException) !! valid)
                                      then Some (s (MemRqT !! memException)
                                                   ((opt MemException) !! data))
                                      else None
                                   |};|}
       else None).
    
    Definition execExecT (s1: <| Struct ExecT |>) (s2: <| Struct Exec |>) :=
      s1 (ExecT !! dst) = s2 (Exec !! data) /\
      s1 (ExecT !! memVAddr) = s2 (Exec !! memVAddr) /\
      s1 (ExecT !! execException) = s2 (Exec !! exception) /\
      s1 (ExecT !! nextPc) = s2 (Exec !! nextPc).
              
    Definition execMemRqT (s1: <| Struct MemRqT |>) (s2: <| Struct Exec |>) :=
      s1 (MemRqT !! dst) = s2 (Exec !! data) /\
      s1 (MemRqT !! memVAddr) = s2 (Exec !! memVAddr) /\
      s1 (MemRqT !! execException) = s2 (Exec !! exception) /\
      s1 (MemRqT !! nextPc) = s2 (Exec !! nextPc).

    Definition rfFromExecT (s: <| Struct ExecT |>) (e: bool) (rf: <| Vector Data RIndexSz |>) :=
      if bool_dec (s (ExecT !! wbEpoch)) e
      then
        if evalExpr (useDst _ (s (ExecT !! inst))%kami_expr)
        then fun x => if weq x (evalExpr (getDst _ (s (ExecT !! inst))%kami_expr))
                      then s (ExecT !! dst)
                      else rf x
        else rf
      else rf.

    Definition rfFromMemRqT (s: <| Struct MemRqT |>) (e: bool) (rf: <| Vector Data RIndexSz |>) :=
      if bool_dec (s (MemRqT !! wbEpoch)) e
      then
        if evalExpr (useDst _ (s (MemRqT !! inst))%kami_expr)
        then fun x => if weq x (evalExpr (getDst _ (s (MemRqT !! inst))%kami_expr))
                      then s (MemRqT !! dst)
                      else rf x
        else rf
      else rf.

    Open Scope fmap.
    Record combined_inv (i s: RegsT): Prop :=
      { modeI: <| Mode |> ;
        modeIFind: modeI === i.[mode] ;

        wbPcI: <| VAddr |> ;
        wbPcIFind: wbPcI === i.[wbPc] ;

        regFileI: <| Vector Data RIndexSz |> ;
        regFileIFind: regFileI === i.[regFile] ;
        regFileS: <| Vector Data RIndexSz |> ;
        
        cStateI: <| CState |> ;
        cStateIFind: cStateI === i.[cState] ;

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

        regFileMatch:
          regFileS = (fun x =>
                        if memRpValid
                        then if weq x (memRpData (MemRpT !! indx))
                             then memRpData (MemRpT !! dst)
                             else regFileI x
                        else regFileI x) ;

        wbEpochI: <| Bool |> ;
        wbEpochIFind: wbEpochI === i.[wbEpoch] ;

        regReadSrc1:
          regReadValid = true ->
          regReadData (RegReadT !! wbEpoch) = wbEpochI ->
          regReadData (RegReadT !! src1) =
          rfFromExecT
            execData
            (execValid && evalExpr (useDst _ (execData (ExecT !! inst))) &&
                       negb (evalExpr (isLd _ (execData (ExecT !! inst)))))
            (rfFromMemRqT
               memRqData
               (memRqValid && evalExpr (useDst _ (execData (ExecT !! inst))) &&
                           negb (evalExpr (isLd _ (memRqData (MemRqT !! inst)))))
               regFileS)
            (evalExpr (getSrc1 _ (regReadData (RegReadT !! inst))%kami_expr)) ;
        
        regReadSrc2:
          regReadValid = true ->
          regReadData (RegReadT !! wbEpoch) = wbEpochI ->
          regReadData (RegReadT !! src2) =
          rfFromExecT
            execData
            (execValid && evalExpr (useDst _ (execData (ExecT !! inst))) &&
                       negb (evalExpr (isLd _ (execData (ExecT !! inst)))))
            (rfFromMemRqT
               memRqData
               (memRqValid && evalExpr (useDst _ (execData (ExecT !! inst))) &&
                           negb (evalExpr (isLd _ (memRqData (MemRqT !! inst)))))
               regFileS)
            (evalExpr (getSrc2 _ (regReadData (RegReadT !! inst))%kami_expr)) ;

        execVal:
          execValid = true ->
          execData (ExecT !! wbEpoch) = wbEpochI ->
          execExecT execData
                    (evalExpr
                       (execFn _ (execData (ExecT !! inst))
                               (rfFromMemRqT memRqData memRqValid regFileS
                                             (evalExpr (getSrc1 _ (execData (ExecT !! inst)))))
                               (rfFromMemRqT memRqData memRqValid regFileS
                                             (evalExpr (getSrc2 _ (execData (ExecT !! inst)))))
                       )%kami_expr) ;

        memRqVal:
          memRqValid = true ->
          memRqData (MemRqT !! wbEpoch) = wbEpochI ->
          execMemRqT memRqData
                     (evalExpr
                        (execFn _ (memRqData (MemRqT !! inst))
                                (regFileS (evalExpr (getSrc1 _ (memRqData (MemRqT !! inst)))))
                                (regFileS (evalExpr (getSrc2 _ (memRqData (MemRqT !! inst)))))
                        )%kami_expr) ;

        wbPcSFind: wbPcI === s.[wbPc] ;
        modeSFind: modeI === s.[mode] ;
        regFileSFind: regFileS === s.[regFile] ;
        cStateSFind: cStateI === s.[cState] ;

        staleList: <[ list (@Stale type) ]> ;
        staleListFind: staleList === s.[stales] ;

        listMatch:
          rmNone (fromMemRqT memRqData memRqValid ::
                             fromExecT execData execValid ::
                             fromRegReadT regReadData regReadValid ::
                             fromFetchRpT fetchRpData fetchRpValid ::
                             fromFetchRqT fetchRqData fetchRqValid ::
                             fromInstVToPRqT instVToPRqData instVToPRqValid :: nil)
          = staleList ;

      }.

    Definition procInlUnfold := ltac:(metaFlatten procFullInl).

    Definition procSpec' :=
      ltac:(let y :=
                eval cbv [processorSpec
                            makeSinModule sinModuleToMetaModule
                            sinRegToMetaReg sinRuleToMetaRule sinMethToMetaMeth
                            sinRegs sinRules sinMeths
                            regGen ruleGen methGen regName ruleName methName
                            map]
            in (sinModuleToMetaModule n processorSpec) in exact y).

    Definition procSpec := ltac:(metaFlatten procSpec').

    Ltac procSpecificUnfold :=
      cbn [fromInstVToPRqT fromFetchRqT fromFetchRpT fromRegReadT fromExecT fromMemRqT] in *.

    Lemma instVToPRq_inv:
      ruleMapInst combined_inv procInlUnfold procSpec instVToPRq.
    Proof.
      (* SKIP_PROOF_OFF *)
      initInvRight procSpec (stalePc).
      rewrite (rmNonePartition 4).
      cbv [partition fst snd].
      simplBoolFalse.
      f_equal.
      instantiate (1 := regV).
      reflexivity.
      (* END_SKIP_PROOF_OFF *)
    Qed.

    Lemma wb_inv:
      ruleMapInst combined_inv procInlUnfold procSpec wb.
    Proof.
      (* SKIP_PROOF_OFF *)
      simplInv; left;
        simplInvHyp;
        simplInvGoal.
      (* END_SKIP_PROOF_OFF *)
    Qed.

    Lemma fetchRq_inv:
      ruleMapInst combined_inv procInlUnfold procSpec fetchRq.
    Proof.
      initInvRight procSpec (staleInstVToP).
      - unfold indexIn.
        cbv [evalExpr].
        rewrite (rmNonePartition 4).
        cbv [partition fst snd].
        rewrite app_length.
        match goal with
        | |- context[(?P + ?Q)%nat] =>
          let cmp := fresh "cmp" in
          assert (cmp: (P < P+Q)%nat) by (simpl in *; Omega.omega);
            instantiate (1 := P)
        end.
        match goal with
        | |- context [if ?P then _ else _] => destruct P; auto
        end.
      - reflexivity.
      - rewrite M.union_empty_L.
        setoid_rewrite (rmNonePartition 4) at 2.
        cbv [partition fst snd].
        unfold rmNone at 3.
        unfold fromInstVToPRqT.
        rewrite nth_len.
        reflexivity.
      - apply M.Disj_empty_2.
      - apply M.Disj_empty_2.
      - admit.
      - 
        right; let X := fresh in intro X; simpl in X;
                                   apply M.F.P.F.empty_in_iff in X.
        assumption.
      - constructor.
          
        repeat f_equal.
        rewrite ?evalExprRewrite.
        match goal with
        | |- context[evalExpr (# (evalExpr ?P))%kami_expr] =>
          idtac
        end.
        rewrite evalExprRewrite.

        rewrite app_length in listMatch.
        Lemma test: forall b, @evalConstT Bool (ConstBool b) = b.
        Proof.
          intros; reflexivity.
        Qed.
        Set Printing Implicit.
        Set Printing All.
        unfold evalConstT.
  End Pf.
End Processor.

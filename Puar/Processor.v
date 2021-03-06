Require Import Kami Lib.Indexer Lib.Struct Kami.Tactics Kami.SemFacts Lib.FMap
        Lib.Reflection Puar.Useful FunctionalExtensionality.

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
Notation readPc := "readPc".
Notation writePc := "writePc".
Notation readWbEpoch := "readWbEpoch".
Notation writeWbEpoch := "writeWbEpoch".
Notation readLongLat := "readLongLat".
Notation writeLongLat := "writeLongLat".
Notation epochsMatch := "epochsMatch".

Notation commit := "commit".

(* Final External method calls *)
Notation getInstVToP := "getInstVToP".
Notation getInst := "getInst".
Notation getMemVToP := "getMemVToP".
Notation memPriv := "memPriv".

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
Notation mode := "mode".
Notation wbPc := "wbPc".
Notation longLat := "longLat".

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
Notation regReadDrop := "regReadDrop".
Notation exec := "exec".
Notation execDrop := "execDrop".
Notation memVToPRqNone := "memVToPRqNone".
Notation wb := "wb".
Notation memRqDrop := "memRqDrop".
Notation longLatStart := "longLatStart".
Notation longLatFinish := "longLatFinish".
Notation longLatDrop := "longLatDrop".

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
Notation staleMemVToPValid := "staleMemVToPValid".
Notation staleMemVToP := "staleMemVToP".
Notation drop := "drop".
Close Scope string.

Section Processor.
  Variable NumDataBytes RIndexSz: nat.
  Variable VAddr PAddr Inst MemRq Mode MemException ExecException FinalException: Kind.
  Definition Data := Bit (8 * NumDataBytes).
  Variable PcInit: ConstT VAddr.
  Variable RegFileInit: ConstT (Vector Data RIndexSz).

  Variable BtbState BpState: Kind.
  Variable BtbStateInit: ConstT BtbState.
  Variable BpStateInit: ConstT BpState.

  Notation RIndex := (Bit RIndexSz).

  Variable getSrc1: forall ty, ty Inst -> RIndex @ ty.
  Variable getSrc2: forall ty, ty Inst -> RIndex @ ty.
  Variable useSrc1: forall ty, ty Inst -> Bool @ ty.
  Variable useSrc2: forall ty, ty Inst -> Bool @ ty.
  Variable useDst: forall ty, ty Inst -> Bool @ ty.
  (* This folds in whether dst is zero or not *)
  Variable getDst: forall ty, ty Inst -> RIndex @ ty.

  Definition Exec := STRUCT
                       { data :: Data;
                         memVAddr :: VAddr;
                         exception :: ExecException;
                         nextPc :: VAddr
                       }.

  Variable isNotLongLat: forall ty, ty Inst -> Bool @ ty.
  Variable execFnNotLongLat execFnLongLat:
    forall ty, ty VAddr -> ty Inst -> ty Data -> ty Data ->
               (Struct Exec) @ ty.

  Definition execFn ty (pc: ty VAddr) (inst: ty Inst) src1 src2 :=
    (IF isNotLongLat _ inst
     then execFnNotLongLat _ pc inst src1 src2
     else execFnLongLat _ pc inst src1 src2)%kami_expr.
  
  Definition VToPRp := STRUCT
                         { pAddr :: PAddr;
                           mode :: Mode;
                           exception :: MemException
                         }.
  
  Variable isLd: forall ty, ty Inst -> Bool @ ty.
  Variable isSt: forall ty, ty Inst -> Bool @ ty.

  Variable getNextBtb: forall ty, ty BtbState -> ty VAddr -> VAddr @ ty.
  Variable updBtb: forall ty, ty BtbState -> ty VAddr -> ty Bool -> ty VAddr -> BtbState @ ty.

  Variable getBp: forall ty, ty BpState -> ty VAddr -> ty Inst -> VAddr @ ty.
  Variable updBp: forall ty, ty BpState -> ty VAddr -> ty Inst -> ty Bool ->
                             ty Bool -> ty VAddr ->
                             BpState @ ty.

  Variable next: forall ty, ty VAddr -> VAddr @ ty.

  Variable useSrc1Means: forall pc i, evalExpr (useSrc1 type i) = false ->
                                      forall s1 s1' s2,
                                        evalExpr (execFn type pc i s1 s2) =
                                        evalExpr (execFn type pc i s1' s2).
  Variable useSrc2Means: forall pc i, evalExpr (useSrc2 type i) = false ->
                                      forall s1 s2 s2',
                                        evalExpr (execFn type pc i s1 s2) =
                                        evalExpr (execFn type pc i s1 s2').
            
  
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
                                  instVToPRp :: Struct VToPRp
                                }.

  Definition FetchRpT := STRUCT { decEpoch :: Bool;
                                  execEpoch :: Bool;
                                  wbEpoch :: Bool;
                                  pc :: VAddr;
                                  nextPc :: VAddr;
                                  instVToPRp :: Struct VToPRp;
                                  inst :: Inst
                                }.

  Definition RegReadT := STRUCT { execEpoch :: Bool;
                                  wbEpoch :: Bool;
                                  pc :: VAddr;
                                  instVToPRp :: Struct VToPRp;
                                  inst :: Inst;
                                  src1 :: Data;
                                  src2 :: Data;
                                  nextPc :: VAddr
                                }.
  
  Definition ExecT := STRUCT { wbEpoch :: Bool;
                               pc :: VAddr;
                               instVToPRp :: Struct VToPRp;
                               inst :: Inst;
                               exec :: Struct Exec
                             }.

  Definition MemRqT := STRUCT { wbEpoch :: Bool;
                                pc :: VAddr;
                                instVToPRp :: Struct VToPRp;
                                inst :: Inst;
                                exec :: Struct Exec;
                                memVToPRp :: optT (Struct VToPRp)
                              }.

  Definition MemRpT := STRUCT { indx :: RIndex;
                                dst :: Data
                              }.

  Definition MemPrivT := STRUCT { pc :: VAddr;
                                  instVToPRp :: Struct VToPRp;
                                  inst :: Inst;
                                  exec :: Struct Exec;
                                  memVToPRp :: optT (Struct VToPRp) }.

  Definition CExec := STRUCT
                        { exception :: Bool;
                          nextPc :: VAddr;
                          dst :: Data
                        }.

  Definition instVToPRqPop := MethodSig (instVToPRq -- pop) (Void): (Struct InstVToPRqT).
  Definition instVToPRqFirst := MethodSig (instVToPRq -- first) (Void): (Struct InstVToPRqT).
  Definition instVToPRpEnq := MethodSig (instVToPRp -- enq) (Struct FetchRqT): Void.
  Definition instRqPop := MethodSig (instRq -- pop) (Void): (Struct FetchRqT).
  Definition instRqFirst := MethodSig (instRq -- first) (Void): (Struct FetchRqT).
  Definition instRpEnq := MethodSig (instRp -- enq) (Struct FetchRpT): Void.

  Definition regReadPop := MethodSig (regRead -- pop) (Void): (Struct RegReadT).
  Definition regReadFirst := MethodSig (regRead -- first) (Void): (Struct RegReadT).
  Definition execEnq := MethodSig (exec -- enq) (Struct ExecT): Void.
  Definition memVToPRqPop := MethodSig (memVToPRq -- pop) (Void): (Struct ExecT).
  Definition memVToPRqFirst := MethodSig (memVToPRq -- first) (Void): (Struct ExecT).
  Definition memVToPRpEnq := MethodSig (memVToPRp -- enq) (Struct MemRqT): Void.
  Definition memRqPop := MethodSig (memRq -- pop) (Void): (Struct MemRqT).
  Definition memRqFirst := MethodSig (memRq -- first) (Void): (Struct MemRqT).
  Definition memRpEnq := MethodSig (memRp -- enq) (optT (Struct MemRpT)): Void.

  Definition instVToPCall := MethodSig getInstVToP (VAddr): Struct VToPRp.
  Definition instCall := MethodSig getInst (PAddr): Inst.
  Definition memVToPCall := MethodSig getMemVToP (VAddr): Struct VToPRp.
  Definition commitCall := MethodSig commit (VAddr): Void.

  Definition callMemPriv := MethodSig memPriv (Struct MemPrivT): Struct CExec.

  Definition readPcCall := MethodSig readPc (Void): VAddr.
  Definition writePcCall := MethodSig writePc (VAddr): Void.
  Definition readWbEpochCall := MethodSig readWbEpoch (Void): Bool.
  Definition writeWbEpochCall := MethodSig writeWbEpoch (Bool): Void.
  Definition readLongLatCall := MethodSig readLongLat (Void): Bool.
  Definition writeLongLatCall := MethodSig writeLongLat (Bool): Void.
  Definition epochsMatchCall := MethodSig epochsMatch (Void): Bool.
  
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
             (ld1 ld2: ty Bool)
             (dst1 dst2 dst3 src: ty RIndex)
             (ud1 ud2: ty Bool)
             (f1d f2d f3d d: ty Data)
             (e1 e2 e: ty Bool) :=
    ( IF (!#ld1 && (#f1Valid && #e1 == #e && #ud1) && #src == #dst1)
      then #f1d else
      IF (!#ld2 && (#f2Valid && #e2 == #e && #ud2) && #src == #dst2)
      then #f2d else
      IF (#f3Valid && #src == #dst3)
      then #f3d else #d
    )%kami_expr.
  
  Definition processor :=
    SIN {
        Register pc : VAddr <- PcInit
        with Register regFile : Vector Data RIndexSz <- RegFileInit
                                        
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

        with Register longLat : Bool <- (ConstBool false)
                                            
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
          Assert (#decEpochVal == #inp1!FetchRpT@.decEpoch
                  && #execEpochVal == #inp1!FetchRpT@.execEpoch
                  && #wbEpochVal == #inp1!FetchRpT@.wbEpoch);                           
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

          LET execUse <- useDst _ execInst;
          LET memRqUse <- useDst _ memRqInst;

          LET src1Val <- getSrc1 _ instVal;
          LET src2Val <- getSrc2 _ instVal;

          LET use1 <- useSrc1 _ instVal;
          LET use2 <- useSrc2 _ instVal;

          LET execData <- #fifoExecData!ExecT@.exec!Exec@.data;
          LET memRqData <- #fifoMemRqData!MemRqT@.exec!Exec@.data;
          LET memRpData <- #fifoMemRpData!MemRpT@.dst;

          LET src1Data <- #regFileVal@[#src1Val];
          LET src2Data <- #regFileVal@[#src2Val];

          LET execWbEpoch <- #fifoExecData!ExecT@.wbEpoch;
          LET memRqWbEpoch <- #fifoMemRqData!MemRqT@.wbEpoch;

          LET stall <-
              (#execLd && (#fifoExecV && #execWbEpoch == #wbEpochVal && #execUse) &&
                ((#use1 && #src1Val == #execDst) || (#use2 && #src2Val == #execDst))) ||
              (#memRqLd && (#fifoMemRqV && #memRqWbEpoch == #wbEpochVal && #memRqUse) &&
                ((#use1 && #src1Val == #memRqDst) || (#use2 && #src2Val == #memRqDst)));

          Assert ! #stall;

          LET bypassSrc1 <-
              bypass _
              fifoExecV fifoMemRqV fifoMemRpV
              execLd memRqLd
              execDst memRqDst memRpDst src1Val
              execUse memRqUse
              execData memRqData memRpData src1Data
              execWbEpoch memRqWbEpoch wbEpochVal;

          LET bypassSrc2 <-
              bypass _
              fifoExecV fifoMemRqV fifoMemRpV
              execLd memRqLd
              execDst memRqDst memRpDst src2Val
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
                                        instVToPRp ::= #inp1!FetchRpT@.instVToPRp;
                                        inst ::= #instVal;
                                        src1 ::= #bypassSrc1;
                                        src2 ::= #bypassSrc2;
                                        nextPc ::= #nextPcVal
                                   });
          Retv

        with Rule regReadDrop :=
          Pop inp1 : Struct FetchRpT <- fifoFetchRp;
          Read decEpochVal <- decEpoch;
          Read execEpochVal <- execEpoch;
          Read wbEpochVal <- wbEpoch;
          Assert ! (#decEpochVal == #inp1!FetchRpT@.decEpoch
                    && #execEpochVal == #inp1!FetchRpT@.execEpoch
                    && #wbEpochVal == #inp1!FetchRpT@.wbEpoch);                           
          Retv

        with Rule exec :=
          Pop inp1 : Struct RegReadT <- fifoRegRead;
          LET instVal <- #inp1!RegReadT@.inst;
          LET src1Val <- #inp1!RegReadT@.src1;
          LET src2Val <- #inp1!RegReadT@.src2;
          LET pcVal' <- #inp1!RegReadT@.pc;
          Read pcVal <- pc;
          Read execEpochVal <- execEpoch;
          Read wbEpochVal <- wbEpoch;
          Assert (isNotLongLat _ instVal);
          Assert (#execEpochVal == #inp1!RegReadT@.execEpoch
                  && #wbEpochVal == #inp1!RegReadT@.wbEpoch);
          LET execVal <- execFnNotLongLat _ pcVal' instVal src1Val src2Val;
            
          Write pc <- (IF #execVal!Exec@.nextPc != #inp1!RegReadT@.nextPc
                       then #execVal!Exec@.nextPc
                       else #pcVal);
          Write execEpoch <- (IF #execVal!Exec@.nextPc != #inp1!RegReadT@.nextPc
                              then ! #execEpochVal
                              else #execEpochVal);
          Enq fifoExec : Struct ExecT <-
                                (STRUCT {
                                     wbEpoch ::= #inp1!RegReadT@.wbEpoch;
                                     pc ::= #inp1!RegReadT@.pc;
                                     instVToPRp ::= #inp1!RegReadT@.instVToPRp;
                                     inst ::= #inp1!RegReadT@.inst;
                                     exec ::= #execVal
                                });
          Retv

        with Rule execDrop :=
          Pop inp1 : Struct RegReadT <- fifoRegRead;
          Read execEpochVal <- execEpoch;
          Read wbEpochVal <- wbEpoch;
          Assert ! (#execEpochVal == #inp1!RegReadT@.execEpoch
                    && #wbEpochVal == #inp1!RegReadT@.wbEpoch);
          Read longLatVal <- longLat;
          Assert ! #longLatVal;
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

        with Method (regRead -- pop) (_: Void): (Struct RegReadT) :=
          Pop inp1 : _ <- fifoRegRead;
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

        with Method (regRead -- first) (_: Void): (Struct RegReadT) :=
          First inp1 : _ <- fifoRegRead;
          Ret #inp1
                
        with Method epochsMatch (_: Void): Bool :=
          First inp1 : _ <- fifoRegRead;
          Read execEpochVal <- execEpoch;
          Read wbEpochVal <- wbEpoch;  
          Ret (#execEpochVal == #inp1!RegReadT@.execEpoch
               && #wbEpochVal == #inp1!RegReadT@.wbEpoch)
                
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

        with Method (exec -- enq) (a: Struct ExecT): Void :=
          First inp1 : _ <- fifoRegRead;
          Enq fifoExec : _ <- #a;
          Read pcVal <- pc;
          Read execEpochVal <- execEpoch;
          Write pc <- (IF #a!ExecT@.exec!Exec@.nextPc != #inp1!RegReadT@.nextPc
                       then #a!ExecT@.exec!Exec@.nextPc
                       else #pcVal);
          Write execEpoch <- (IF #a!ExecT@.exec!Exec@.nextPc != #inp1!RegReadT@.nextPc
                              then !#execEpochVal
                              else #execEpochVal);
          Retv    

        with Method (memVToPRp -- enq) (a: Struct MemRqT): Void :=
          Enq fifoMemRq : _ <- #a;
          Retv

        with Method (memRp -- enq) (a: optT (Struct MemRpT)): Void :=
          Read x : Bool <- (fifoMemRp ++ Valid)%string;
          Assert ! #x;
          Write fifoMemRp: (Struct MemRpT) <- getSome #a;
          Write (fifoMemRp ++ Valid)%string <- isSome #a;
          Retv

        with Method readPc (_: Void): VAddr :=
          Read pcVal <- pc;
          Ret #pcVal

        with Method writePc (a: VAddr): Void :=
          Write pc <- #a;
          Retv
                 
        with Method readWbEpoch (_: Void): Bool :=
          Read wbEpochVal <- wbEpoch;
          Ret #wbEpochVal

        with Method writeWbEpoch (a: Bool): Void :=
          Write wbEpoch <- #a;
          Retv

        with Method readLongLat (_: Void): Bool :=
          Read longLatVal <- longLat;    
          Ret #longLatVal

        with Method writeLongLat (a: Bool): Void :=
          Write longLat <- #a;    
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
                                 instVToPRp ::= #inp2
                            });
          Retv }.
                                 
  Definition InstCall :=
    SIN {
        Rule fetchRp :=
          Call _ <- instRqFirst();
          Call inp1 <- instRqPop();
          Call inp2 <- instCall(#inp1!FetchRqT@.instVToPRp!VToPRp@.pAddr);
          Call instRpEnq(STRUCT {
                             decEpoch ::= #inp1!FetchRqT@.decEpoch;
                             execEpoch ::= #inp1!FetchRqT@.execEpoch;
                             wbEpoch ::= #inp1!FetchRqT@.wbEpoch;
                             pc ::= #inp1!FetchRqT@.pc;
                             nextPc ::= #inp1!FetchRqT@.nextPc;
                             instVToPRp ::= #inp1!FetchRqT@.instVToPRp;
                             inst ::= #inp2
                        });
          Retv }.

  Definition LongLatency :=
    SIN {
        Rule longLatStart :=
          Call inp1 <- regReadFirst();
          LET instVal <- #inp1!RegReadT@.inst;
          Assert (! (isNotLongLat _ instVal));
          Call longLatVal <- readLongLatCall();
          Assert !#longLatVal;
          Call writeLongLatCall($$ true);
          Retv
            
        with Rule longLatFinish :=
          Call epochsMatchVal <- epochsMatchCall();
          Assert #epochsMatchVal;
          Call inp1 <- regReadPop();
          LET pcVal <- #inp1!RegReadT@.pc;
          LET instVal <- #inp1!RegReadT@.inst;
          LET src1Val <- #inp1!RegReadT@.src1;
          LET src2Val <- #inp1!RegReadT@.src2;
          Assert (! (isNotLongLat _ instVal));
          Call longLatVal <- readLongLatCall();
          Assert #longLatVal;
          Call writeLongLatCall($$ false);
          
          LET execVal <- execFnLongLat _ pcVal instVal src1Val src2Val;
          Call execEnq(STRUCT {
                           wbEpoch ::= #inp1!RegReadT@.wbEpoch;
                           pc ::= #inp1!RegReadT@.pc;
                           instVToPRp ::= #inp1!RegReadT@.instVToPRp;
                           inst ::= #inp1!RegReadT@.inst;
                           exec ::= #execVal
                      });
          Retv

        with Rule longLatDrop :=
          Call epochsMatchVal <- epochsMatchCall();
          Assert !#epochsMatchVal;
          Call inp1 <- regReadPop();
          Call longLatVal <- readLongLatCall();
          Assert #longLatVal;
          Call writeLongLatCall($$ false);
          Retv
      }.

  Definition MemVToPCall :=
    SIN {
        Rule memVToPRq :=
          Call inp1 <- memVToPRqPop();
          LET instVal <- #inp1!ExecT@.inst;
          Assert (isLdSt _ instVal);
          Call inp2 <- memVToPCall(#inp1!ExecT@.exec!Exec@.memVAddr);
          Call memVToPRpEnq(STRUCT {
                                wbEpoch ::= #inp1!ExecT@.wbEpoch;
                                pc ::= #inp1!ExecT@.pc;
                                instVToPRp ::= #inp1!ExecT@.instVToPRp;  
                                inst ::= #inp1!ExecT@.inst;
                                exec ::= #inp1!ExecT@.exec;
                                memVToPRp ::= some #inp2
                           });
          Retv
            
        with Rule memVToPRqNone :=
          Call _ <- memVToPRqFirst();
          Call inp1 <- memVToPRqPop();
          LET instVal <- #inp1!ExecT@.inst;
          Assert ! (isLdSt _ instVal);
          Call memVToPRpEnq(STRUCT {
                                wbEpoch ::= #inp1!ExecT@.wbEpoch;
                                pc ::= #inp1!ExecT@.pc;
                                instVToPRp ::= #inp1!ExecT@.instVToPRp;  
                                inst ::= #inp1!ExecT@.inst;
                                exec ::= #inp1!ExecT@.exec;
                                memVToPRp ::= none
                           });
          Retv
      }.
                                 
  Definition MemCall :=
    SIN {
        Register wbPc : VAddr <- PcInit
                                  
        with Rule memRq :=
          Call _ <- memRqFirst();
          Call inp1 <- memRqPop();
          Call wbEpochVal <- readWbEpochCall();
          Read wbPcVal <- wbPc;

          LET pcVal : VAddr <- #inp1!MemRqT@.pc;
          LET instVToPRpVal <- #inp1!MemRqT@.instVToPRp;
          LET instVal <- #inp1!MemRqT@.inst;
          LET nextPcVal <- #inp1!MemRqT@.exec!Exec@.nextPc;
          LET execExceptionVal <- #inp1!MemRqT@.exec!Exec@.exception;
          LET memVAddrVal <- #inp1!MemRqT@.exec!Exec@.memVAddr;
          LET memVToPRpVal <- #inp1!MemRqT@.memVToPRp;
          LET dstVal <- #inp1!MemRqT@.exec!Exec@.data;

          Call pcRegVal <- readPcCall();

          Call cExecVal <- callMemPriv(STRUCT {
                pc ::= #pcVal;
                instVToPRp ::= #instVToPRpVal;
                inst ::= #instVal;
                exec ::= (#inp1!MemRqT@.exec);
                memVToPRp ::= #memVToPRpVal });
          
          Call writeWbEpochCall(IF #cExecVal!CExec@.exception
                                then ! #wbEpochVal
                                else #wbEpochVal);
          Call writePcCall(IF #cExecVal!CExec@.exception
                           then #cExecVal!CExec@.nextPc
                           else #pcRegVal);

          Assert (#wbEpochVal == #inp1!MemRqT@.wbEpoch);

          Assert (#wbPcVal == #inp1!MemRqT@.pc);
                  
          Write wbPc <- (#cExecVal!CExec@.nextPc);

          Call memRpEnq(STRUCT { valid ::= (! #cExecVal!CExec@.exception) &&
                                       useDst _ instVal;
                                 data ::= STRUCT { indx ::= getDst _ instVal;
                                                   dst ::=
                                                       IF (isLd _ instVal)
                                                       then #cExecVal!CExec@.dst
                                                       else #dstVal }
                       });

          Read btbStateVal: BtbState <- btb;
          LET isException <- #cExecVal!CExec@.exception;
          LET nextPcVal: VAddr <- #cExecVal!CExec@.nextPc;
          Write btb <- updBtb _ btbStateVal pcVal isException nextPcVal;
          
          LET isTaken <- #nextPcVal != next _ pcVal;
          Read bpStateVal: BpState <- bp;
          Write bp <- updBp _ bpStateVal pcVal instVal isException isTaken nextPcVal;
          
          (* Call commitCall(#inp1!MemRqT@.pc); *)

          (* If ! (isSome #cExecVal!CExec@.exception) *)
          (* then ( *)
          (*   Call cmdNonUserCall(#cExecVal!CExec@.cmdNonUser); *)
          (*   Call cmdInstCall(#cExecVal!CExec@.cmdInst); *)
          (*   Call cmdDataCall(#cExecVal!CExec@.cmdData); *)
                  
          (*   If isLdSt _ instVal *)
          (*   then ( *)
          (*     Call inp2 <- memCall(createMemRq _ instVal memPAddrVal dstVal); *)
          (*     Ret #inp2 *)
          (*     ) *)
          (*   else ( *)
          (*     Ret $$ Default *)
          (*     ) *)
          (*   as inp2; *)
          (*   LET finalDst <- IF isLd _ instVal *)
          (*                   then #inp2 *)
          (*                   else #inp1!MemRqT@.exec!Exec@.data; *)

          (*   If (useDst _ instVal) *)
          (*   then (Call memRpEnq(STRUCT { indx ::= getDst _ instVal; *)
          (*                                dst ::= #finalDst *)
          (*                      }); Retv); *)
          (*   Retv *)
          (* );   *)
          Retv  

        with Rule memRqDrop :=
          Call _ <- memRqFirst();
          Call inp1 <- memRqPop();
          (* Read wbPcVal <- wbPc; *)
          (* Assert ! (#wbPcVal == #inp1!MemRqT@.pc); *)
          Call wbEpochVal <- readWbEpochCall();
          Assert ! (#wbEpochVal == #inp1!MemRqT@.wbEpoch);
          Retv

      }.


  Record Stale ty := { sPc: ty VAddr ;
                       sInstVToP: ty (optT (Struct VToPRp)) ;
                       sInst: option (ty Inst) ;
                       sMemVAddr: option (ty VAddr) ;
                       sMemVToP: ty (optT (Struct VToPRp))
                     }.

  Definition newStalePc {ty} (val: ty VAddr) (val2: ty (optT (Struct VToPRp)))
    := {| sPc := val;
          sInstVToP := val2;
          sInst := None;
          sMemVAddr := None;
          sMemVToP := val2 |}.

  Definition updInstVToP {ty} (s: Stale ty) val :=
    {| sPc := sPc s;
       sInstVToP := val;
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
       sMemVToP := val |}.

  Notation StaleT ty val val2 := (@NativeKind (Stale ty) (newStalePc val val2)).
  Notation StaleT' val val2 := (StaleT _ val val2).
  Notation Stales ty := (@NativeKind (list (Stale ty)) nil).
  Notation Stales' := (Stales _).

  Notation NativeVar ntype nval := (Var _ (@NativeKind ntype nval) nval).

  Definition processorSpec :=
    SIN {
        Register wbPc : VAddr <- PcInit
        with Register regFile : Vector Data RIndexSz <- RegFileInit

        with RegisterN stales : Stales type <- (NativeConst nil nil)

        with Rule stalePc :=
          ReadN stalesVal : Stales' <- stales;
          Nondet vAddr: SyntaxKind VAddr;
          LET defVToP: (optT (Struct VToPRp)) <- none;
          WriteN stales : _ <- Var _ Stales' (stalesVal ++ [newStalePc vAddr defVToP]);
          Retv

        with Rule staleInstVToP :=
          ReadN stalesVal : Stales' <- stales;
          Nondet i: @NativeKind nat 0;
          Assert $$ (indexIn i stalesVal);
          LET vAddrDef : VAddr <- $$ Default;
          LET defVToP: (optT (Struct VToPRp)) <- none;
          Call inp <- instVToPCall(#(sPc (nth i stalesVal (newStalePc vAddrDef defVToP))));
          LET updVal <- some #inp;
          WriteN stales : _ <- Var _ Stales' (nth_upd updInstVToP updVal i stalesVal);
          Retv

        with Rule staleInst :=
          ReadN stalesVal : Stales' <- stales;
          Nondet i: @NativeKind nat 0;
          Assert $$ (indexIn i stalesVal);
          LET vAddrDef : VAddr <- $$ Default;
          LET defVToP: (optT (Struct VToPRp)) <- none;
          Call inp <- instCall((getSome #(sInstVToP
                                            (nth i stalesVal
                                                 (newStalePc vAddrDef defVToP))))!VToPRp@.pAddr);
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
          LET defVToP: (optT (Struct VToPRp)) <- none;
          Assert $$ (isValid (sMemVAddr (nth i stalesVal (newStalePc vAddrDef defVToP))));
          Call inp <- memVToPCall(#(rmSome
                                      vAddrDef
                                      (sMemVAddr (nth i stalesVal
                                                      (newStalePc vAddrDef defVToP)))));
          LET realVToP: (optT (Struct VToPRp)) <- some #inp;
          WriteN stales : _ <- Var _ Stales' (nth_upd updMemVToP realVToP i stalesVal);
          Retv

        with Rule drop :=
          ReadN stalesVal : Stales' <- stales;
          Nondet i: @NativeKind nat 0;
          WriteN stales : _ <- Var _ Stales' (rmList i stalesVal);
          LET vAddrDef : VAddr <- $$ Default;
          LET defVToP: (optT (Struct VToPRp)) <- none;
          LETN entry : (StaleT' vAddrDef defVToP) <- Var _ (StaleT' vAddrDef defVToP)
                                          (hd (newStalePc vAddrDef defVToP) stalesVal);
          Retv
            
        with Rule memRq :=
          ReadN stalesVal : Stales' <- stales;

          Read wbPcVal: VAddr <- wbPc;
          Read regFileVals: Vector Data RIndexSz <- regFile;

          LET vAddrDef : VAddr <- $$ Default;
          LET defVToP: (optT (Struct VToPRp)) <- none;
          LETN inp1 : _ <- Var _ (StaleT' vAddrDef defVToP)
                        (hd (newStalePc vAddrDef defVToP) stalesVal);
          LET pAddrDef: PAddr <- $$ Default;
          (* LET xlateInfo: XlateInfo <- $$ Default ; *)
          LET instDef: Inst <- $$ Default;

          LET pcVal <- #(sPc inp1);
          LET instVToPRpVal <- getSome #(sInstVToP inp1);
          LET instVal <- #(rmSome instDef (sInst inp1));
          LET memVAddrVal1 <- #(rmSome vAddrDef (sMemVAddr inp1));
          LET memVToPRpVal <- #(sMemVToP inp1);

          LET src1Val <- #regFileVals@[getSrc1 _ instVal];
          LET src2Val <- #regFileVals@[getSrc2 _ instVal];

          LET execVal <- execFn _ pcVal instVal src1Val src2Val;

          LET nextPcVal <- #execVal!Exec@.nextPc;
          LET execExceptionVal <- #execVal!Exec@.exception;
          LET memVAddrVal <- #execVal!Exec@.memVAddr;
          LET dstVal <- #execVal!Exec@.data;

            
          Assert $$ (notNil stalesVal);
          Assert (isSome #(sInstVToP inp1));
          Assert $$ (isValid (sInst inp1));

          Assert ! (isLdSt _ instVal) || $$ (isValid (sMemVAddr inp1));
          Assert ! (isLdSt _ instVal) || (isSome #(sMemVToP inp1));
          Assert ! (isLdSt _ instVal) || #memVAddrVal == #memVAddrVal1;

          Call cExecVal <- callMemPriv(STRUCT {
                pc ::= #pcVal;
                instVToPRp ::= #instVToPRpVal;
                inst ::= #instVal;
                exec ::= #execVal;
                memVToPRp ::= #memVToPRpVal });

          Assert (#wbPcVal == #pcVal);

          Write wbPc <- #cExecVal!CExec@.nextPc;

          Write regFile <- IF ((! #cExecVal!CExec@.exception) && useDst _ instVal)
                           then #regFileVals@[getDst _ instVal <-
                                  IF (isLd _ instVal)
                                  then #cExecVal!CExec@.dst
                                  else #dstVal]
                           else #regFileVals;

          (* Call commitCall(#pcVal); *)

          (* If ! (isSome #cExecVal!CExec@.exception) *)
          (* then ( *)
          (*   Call cmdNonUserCall(#cExecVal!CExec@.cmdNonUser); *)
          (*   Call cmdInstCall(#cExecVal!CExec@.cmdInst); *)
          (*   Call cmdDataCall(#cExecVal!CExec@.cmdData); *)
            
          (*   If isLdSt _ instVal *)
          (*   then ( *)
          (*     Call inp2 <- memCall(createMemRq _ instVal memPAddrVal dstVal); *)
          (*     Ret #inp2 *)
          (*     ) *)
          (*   else ( *)
          (*     Ret $$ Default *)
          (*     ) *)
          (*   as inp2; *)
          (*   LET finalDst <- IF isLd _ instVal *)
          (*                   then #inp2 *)
          (*                   else #dstVal; *)

          (*   If (useDst _ instVal) *)
          (*   then ( *)
          (*     Write regFile <- #regFileVals@[getDst _ instVal <- #finalDst]; *)
          (*     Retv *)
          (*     ); *)
          (*    Retv *)
          (*   ); *)

          WriteN stales : _ <- Var _ Stales' (tl stalesVal);
          Retv
      }.

  Section Pf.
    Variable n: nat.
    Notation single := (sinModuleToMetaModule n).
    Notation proc := (single processor).
    Notation instVToPCall := (single InstVToPCall).
    Notation instCall := (single InstCall).
    Notation longLatency := (single LongLatency).
    Notation memVToPCall := (single MemVToPCall).
    Notation memCall := (single MemCall).

    Notation procFull := ((MetaMod proc)
                            ++++ (MetaMod instVToPCall)
                            ++++ (MetaMod instCall)
                            ++++ (MetaMod longLatency)
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

    Local Definition procFullInl'1: MetaModule.
    Proof.
      start_def procFullFlat.

      ssF newCbv (instVToPRq -- pop) "fetchRq"%string.
      ssF newCbv (instVToPRq -- first) "fetchRq"%string.
      ssF newCbv (instVToPRp -- enq) "fetchRq"%string.

      ssF newCbv (instRq -- pop) "fetchRp"%string.
      ssF newCbv (instRq -- first) "fetchRp"%string.
      ssF newCbv (instRp -- enq) "fetchRp"%string.

      ssF newCbv (regRead -- first) "longLatStart"%string.
      ssNoF newCbv "readLongLat"%string "longLatStart"%string.
      ssNoF newCbv "writeLongLat"%string "longLatStart"%string.

      ssNoF newCbv "epochsMatch"%string "longLatDrop"%string.
      ssNoF newCbv (regRead -- pop) "longLatDrop"%string.
      ssNoF newCbv "readLongLat"%string "longLatDrop"%string.
      ssNoF newCbv "writeLongLat"%string "longLatDrop"%string.

      ssF newCbv "epochsMatch"%string "longLatFinish"%string.
      ssF newCbv (regRead -- pop) "longLatFinish"%string.
      ssF newCbv (exec -- enq) "longLatFinish"%string.
      ssF newCbv "readLongLat"%string "longLatFinish"%string.
      ssF newCbv "writeLongLat"%string "longLatFinish"%string.

      ssNoF newCbv (memVToPRq -- pop) "memVToPRq"%string.
      ssNoF newCbv (memVToPRp -- enq) "memVToPRq"%string.

      ssF newCbv (memVToPRq -- pop) "memVToPRqNone"%string.
      ssF newCbv (memVToPRq -- first) "memVToPRqNone"%string.
      ssF newCbv (memVToPRp -- enq) "memVToPRqNone"%string.

      ssNoF newCbv (memRq -- pop) "memRqDrop"%string.
      ssNoF newCbv (memRq -- first) "memRqDrop"%string.
      ssNoF newCbv "readWbEpoch"%string "memRqDrop"%string.

      ssF newCbv (memRp -- enq) "memRq"%string.

      finish_def.
    Defined.
      
    Local Definition procFullInl'4 := ltac:(let y := eval cbv [procFullInl'1] in
                                    procFullInl'1 in exact y).

    Local Definition procFullInl': MetaModule.
    Proof.
      start_def procFullInl'4.

      ssF newCbv (memRq -- pop) "memRq"%string.
      ssF newCbv (memRq -- first) "memRq"%string.

      ssF newCbv "readPc"%string "memRq"%string.
      ssF newCbv "writePc"%string "memRq"%string.
      ssF newCbv "readWbEpoch"%string "memRq"%string.
      ssF newCbv "writeWbEpoch"%string "memRq"%string.

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

      ssFilt newCbv (instVToPRq -- pop) "fetchRq"%string;
      ssFilt newCbv (instVToPRq -- first) "fetchRq"%string.
      ssFilt newCbv (instVToPRp -- enq) "fetchRq"%string.

      ssFilt newCbv (instRq -- pop) "fetchRp"%string.
      ssFilt newCbv (instRq -- first) "fetchRp"%string.
      ssFilt newCbv (instRp -- enq) "fetchRp"%string.

      ssFilt newCbv (regRead -- first) "longLatStart"%string.
      ssNoFilt newCbv "readLongLat"%string "longLatStart"%string.
      ssNoFilt newCbv "writeLongLat"%string "longLatStart"%string.

      ssNoFilt newCbv "epochsMatch"%string "longLatDrop"%string.
      ssNoFilt newCbv (regRead -- pop) "longLatDrop"%string.
      ssNoFilt newCbv "readLongLat"%string "longLatDrop"%string.
      ssNoFilt newCbv "writeLongLat"%string "longLatDrop"%string.

      ssFilt newCbv "epochsMatch"%string "longLatFinish"%string.
      ssFilt newCbv (regRead -- pop) "longLatFinish"%string.
      ssFilt newCbv (exec -- enq) "longLatFinish"%string.
      ssFilt newCbv "readLongLat"%string "longLatFinish"%string.
      ssFilt newCbv "writeLongLat"%string "longLatFinish"%string.
      
      ssNoFilt newCbv (memVToPRq -- pop) "memVToPRq"%string.
      ssNoFilt newCbv (memVToPRp -- enq) "memVToPRq"%string.

      ssFilt newCbv (memVToPRq -- pop) "memVToPRqNone"%string.
      ssFilt newCbv (memVToPRq -- first) "memVToPRqNone"%string.
      ssFilt newCbv (memVToPRp -- enq) "memVToPRqNone"%string.

      ssNoFilt newCbv (memRq -- pop) "memRqDrop"%string.
      ssNoFilt newCbv (memRq -- first) "memRqDrop"%string.
      ssNoFilt newCbv "readWbEpoch"%string "memRqDrop"%string.

      ssFilt newCbv (memRp -- enq) "memRq"%string.      
      ssFilt newCbv (memRq -- pop) "memRq"%string.
      ssFilt newCbv (memRq -- first) "memRq"%string.

      ssFilt newCbv "readPc"%string "memRq"%string.
      ssFilt newCbv "writePc"%string "memRq"%string.
      ssFilt newCbv "readWbEpoch"%string "memRq"%string.
      ssFilt newCbv "writeWbEpoch"%string "memRq"%string.

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

    Lemma instVToPCall_ModEquiv:
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

    Lemma longLatency_ModEquiv:
    MetaModPhoasWf longLatency.
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
                 sInstVToP := evalExpr none;
                 sInst := None;
                 sMemVAddr := None;
                 sMemVToP := evalExpr none |}
       else None).

    Definition some ty K (val: K @ ty) := STRUCT {"valid" ::= $$ true; "data" ::= val}%kami_expr.
                 
    Definition fromFetchRqT (s: <| Struct FetchRqT |>) (v: bool) :=
      (if v then
         Some {| sPc := s (FetchRqT !! pc);
                 sInstVToP := evalExpr (@some _ (Struct VToPRp) #(s (FetchRqT !! instVToPRp))%kami_expr);
                 sInst := None;
                 sMemVAddr := None;
                 sMemVToP := evalExpr none |}
       else None).
    
    Definition fromFetchRpT (s: <| Struct FetchRpT |>) (v: bool) :=
      (if v then
         Some {| sPc := s (FetchRpT !! pc);
                 sInstVToP := evalExpr (@some _ (Struct VToPRp) #(s (FetchRpT !! instVToPRp))%kami_expr);
                 sInst := Some (s (FetchRpT !! inst));
                 sMemVAddr := None;
                 sMemVToP := evalExpr none |}
       else None).
    
    Definition fromRegReadT (s: <| Struct RegReadT |>) (v: bool) :=
      (if v then
         Some {| sPc := s (RegReadT !! pc);
                 sInstVToP := evalExpr (@some _ (Struct VToPRp) #(s (RegReadT !! instVToPRp))%kami_expr);
                 sInst := Some (s (RegReadT !! inst));
                 sMemVAddr := None;
                 sMemVToP := evalExpr none |}
       else None).
    
    Definition fromExecT (s: <| Struct ExecT |>) (v: bool) :=
      (if v then
         Some {| sPc := s (ExecT !! pc);
                 sInstVToP := evalExpr (@some _ (Struct VToPRp) #(s (ExecT !! instVToPRp))%kami_expr);
                 sInst := Some (s (ExecT !! inst));
                 sMemVAddr := Some (s (ExecT !! exec) (Exec !! memVAddr));
                 sMemVToP := evalExpr none |}
       else None).
    
    Definition fromMemRqT (s: <| Struct MemRqT |>) (v: bool) :=
      (if v then
         Some {| sPc := s (MemRqT !! pc);
                 sInstVToP := evalExpr (@some _ (Struct VToPRp) #(s (MemRqT !! instVToPRp))%kami_expr);
                 sInst := Some (s (MemRqT !! inst));
                 sMemVAddr := Some (s (MemRqT !! exec) (Exec !! memVAddr));
                 sMemVToP := s (MemRqT !! memVToPRp)
              |}
       else None).
    
    Definition rfFromExecT (s: <| Struct ExecT |>) (e: bool) (rf: <| Vector Data RIndexSz |>)
               x :=
      if e && (if weq x (evalExpr (getDst _ (s (ExecT !! inst)))) then true else false)
      then s (ExecT !! exec) (Exec !! data)
      else rf x.

    Definition rfFromMemRqT (s: <| Struct MemRqT |>) (e: bool) (rf: <| Vector Data RIndexSz |>)
               x :=
      if e && (if weq x (evalExpr (getDst _ (s (MemRqT !! inst)))) then true else false)
      then s (MemRqT !! exec) (Exec !! data)
      else rf x.

    Open Scope fmap.
    Record combined_inv (i s: RegsT): Prop :=
      { wbPcI: <| VAddr |> ;
        wbPcIFind: wbPcI === i.[wbPc] ;

        regFileI: <| Vector Data RIndexSz |> ;
        regFileIFind: regFileI === i.[regFile] ;
        regFileS: <| Vector Data RIndexSz |> ;
        
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
                        if memRpValid && (if weq x (memRpData (MemRpT !! indx))
                                          then true
                                          else false)
                        then memRpData (MemRpT !! dst)
                        else regFileI x) ;

        wbEpochI: <| Bool |> ;
        wbEpochIFind: wbEpochI === i.[wbEpoch] ;

        regReadSrc1:
          regReadValid = true ->
          regReadData (RegReadT !! wbEpoch) = wbEpochI ->
          evalExpr (useSrc1 _ (regReadData (RegReadT !! inst))) = true ->
          regReadData (RegReadT !! src1) =
          rfFromExecT
            execData
            (negb (evalExpr (isLd _ (execData (ExecT !! inst))))
                  && (execValid
                        && (if bool_dec (execData (ExecT !! wbEpoch)) wbEpochI
                            then true
                            else false)
                        && evalExpr (useDst _ (execData (ExecT !! inst)))))
            (rfFromMemRqT
               memRqData
               (negb (evalExpr (isLd _ (memRqData (MemRqT !! inst))))
                     && (memRqValid
                           && (if bool_dec (memRqData (MemRqT !! wbEpoch)) wbEpochI
                               then true
                               else false)
                           && evalExpr (useDst _ (memRqData (MemRqT !! inst)))))
               regFileS)
            (evalExpr (getSrc1 _ (regReadData (RegReadT !! inst))%kami_expr)) ;
        
        regReadSrc2:
          regReadValid = true ->
          regReadData (RegReadT !! wbEpoch) = wbEpochI ->
          evalExpr (useSrc2 _ (regReadData (RegReadT !! inst))) = true ->
          regReadData (RegReadT !! src2) =
          rfFromExecT
            execData
            (negb (evalExpr (isLd _ (execData (ExecT !! inst))))
                  && (execValid
                        && (if bool_dec (execData (ExecT !! wbEpoch)) wbEpochI
                            then true
                            else false)
                        && evalExpr (useDst _ (execData (ExecT !! inst)))))
            (rfFromMemRqT
               memRqData
               (negb (evalExpr (isLd _ (memRqData (MemRqT !! inst))))
                     && (memRqValid
                           && (if bool_dec (memRqData (MemRqT !! wbEpoch)) wbEpochI
                               then true
                               else false)
                           && evalExpr (useDst _ (memRqData (MemRqT !! inst)))))
               regFileS)
            (evalExpr (getSrc2 _ (regReadData (RegReadT !! inst))%kami_expr)) ;

        regReadNoStall:
          regReadValid = true ->
          ((evalExpr (isLd _ (execData (ExecT !! inst))))
             && (execValid
                   && (if bool_dec (execData (ExecT !! wbEpoch)) wbEpochI
                       then true
                       else false)
                   && evalExpr (useDst _ (execData (ExecT !! inst)))) &&
             ((evalExpr (useSrc1 _ (regReadData (RegReadT !! inst))))
                && (evalExpr (getSrc1 _ (regReadData (RegReadT !! inst)) ==
                              getDst _ (execData (ExecT !! inst)))%kami_expr) ||
               (evalExpr (useSrc2 _ (regReadData (RegReadT !! inst))))
                 && (evalExpr (getSrc2 _ (regReadData (RegReadT !! inst)) ==
                               getDst _ (execData (ExecT !! inst)))%kami_expr)
          ))
          || ((evalExpr (isLd _ (memRqData (MemRqT !! inst))))
                && (memRqValid
                      && (if bool_dec (memRqData (MemRqT !! wbEpoch)) wbEpochI
                          then true
                          else false)
                      && evalExpr (useDst _ (memRqData (MemRqT !! inst)))) &&
                ((evalExpr (useSrc1 _ (regReadData (RegReadT !! inst))))
                   && (evalExpr (getSrc1 _ (regReadData (RegReadT !! inst)) ==
                                 getDst _ (memRqData (MemRqT !! inst)))%kami_expr) ||
                 (evalExpr (useSrc2 _ (regReadData (RegReadT !! inst))))
                   && (evalExpr (getSrc2 _ (regReadData (RegReadT !! inst)) ==
                                 getDst _ (memRqData (MemRqT !! inst)))%kami_expr)
             )) = false ;
        
        execNoStall:
          execValid = true ->
          ((evalExpr (isLd _ (memRqData (MemRqT !! inst))))
             && (memRqValid
                   && (if bool_dec (memRqData (MemRqT !! wbEpoch)) wbEpochI
                       then true
                       else false)
                   && evalExpr (useDst _ (memRqData (MemRqT !! inst)))) &&
             ((evalExpr (useSrc1 _ (execData (ExecT !! inst))))
                && (evalExpr (getSrc1 _ (execData (ExecT !! inst)) ==
                              getDst _ (memRqData (MemRqT !! inst)))%kami_expr) ||
              (evalExpr (useSrc2 _ (execData (ExecT !! inst))))
                && (evalExpr (getSrc2 _ (execData (ExecT !! inst)) ==
                              getDst _ (memRqData (MemRqT !! inst)) )%kami_expr)
          )) = false ;
        
        execVal:
          execValid = true ->
          execData (ExecT !! wbEpoch) = wbEpochI ->
          execData (ExecT !! exec) = 
          evalExpr
            (execFn _ (execData (ExecT !! pc)) (execData (ExecT !! inst))
                    (rfFromMemRqT
                       memRqData
                       (negb (evalExpr (isLd _ (memRqData (MemRqT !! inst))))
                             && (memRqValid
                                   && (if bool_dec (memRqData (MemRqT !! wbEpoch))
                                                   wbEpochI
                                       then true
                                       else false)
                                   && evalExpr
                                   (useDst _ (memRqData (MemRqT !! inst)))))           
                       regFileS (evalExpr (getSrc1 _ (execData (ExecT !! inst)))))
                    (rfFromMemRqT
                       memRqData
                       (negb (evalExpr (isLd _ (memRqData (MemRqT !! inst))))
                             && (memRqValid
                                   && (if bool_dec (memRqData (MemRqT !! wbEpoch))
                                                    wbEpochI
                                       then true
                                       else false)
                                   && evalExpr
                                   (useDst _ (memRqData (MemRqT !! inst)))))           
                       regFileS
                       (evalExpr (getSrc2 _ (execData (ExecT !! inst)))))) ;

        memRqVal:
          memRqValid = true ->
          memRqData (MemRqT !! wbEpoch) = wbEpochI ->
          memRqData (MemRqT !! exec) =
          evalExpr
            (execFn _ (memRqData (MemRqT !! pc)) (memRqData (MemRqT !! inst))
                    (regFileS (evalExpr (getSrc1 _ (memRqData (MemRqT !! inst)))))
                    (regFileS (evalExpr (getSrc2 _ (memRqData (MemRqT !! inst)))))) ;
        
        wbPcSFind: wbPcI === s.[wbPc] ;
        regFileSFind: regFileS === s.[regFile] ;

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

        nonMemVToPRpDef:
          memRqValid = true ->
          memRqData (MemRqT !! memVToPRp) ((opt (Struct VToPRp)) !! valid) = false ->
          memRqData (MemRqT !! memVToPRp) ((opt (Struct VToPRp)) !! data) =
          evalExpr (($$ Default)%kami_expr: (Struct VToPRp) @ type) ;

        nonMemVToPRpLdSt:
          memRqValid = true ->
          evalExpr (isLdSt _ (memRqData (MemRqT !! inst))) = true ->
          memRqData (MemRqT !! memVToPRp) ((opt (Struct VToPRp)) !! valid) = true ;

        memRq_exec:
          memRqValid = true ->
          execValid = true ->
          memRqData (MemRqT !! wbEpoch) = wbEpochI ->
          execData (ExecT !! wbEpoch) = wbEpochI ;

        memRq_regRead:
          memRqValid = true ->
          regReadValid = true ->
          memRqData (MemRqT !! wbEpoch) = wbEpochI ->
          regReadData (RegReadT !! wbEpoch) = wbEpochI ;

        memRq_fetchRp:
          memRqValid = true ->
          fetchRpValid = true ->
          memRqData (MemRqT !! wbEpoch) = wbEpochI ->
          fetchRpData (FetchRpT !! wbEpoch) = wbEpochI ;

        memRq_fetchRq:
          memRqValid = true ->
          fetchRqValid = true ->
          memRqData (MemRqT !! wbEpoch) = wbEpochI ->
          fetchRqData (FetchRqT !! wbEpoch) = wbEpochI ;

        memRq_instVToPRq:
          memRqValid = true ->
          instVToPRqValid = true ->
          memRqData (MemRqT !! wbEpoch) = wbEpochI ->
          instVToPRqData (InstVToPRqT !! wbEpoch) = wbEpochI ;

        exec_regRead:
          execValid = true ->
          regReadValid = true ->
          execData (ExecT !! wbEpoch) = wbEpochI ->
          regReadData (RegReadT !! wbEpoch) = wbEpochI ;

        exec_fetchRp:
          execValid = true ->
          fetchRpValid = true ->
          execData (ExecT !! wbEpoch) = wbEpochI ->
          fetchRpData (FetchRpT !! wbEpoch) = wbEpochI ;

        exec_fetchRq:
          execValid = true ->
          fetchRqValid = true ->
          execData (ExecT !! wbEpoch) = wbEpochI ->
          fetchRqData (FetchRqT !! wbEpoch) = wbEpochI ;

        exec_instVToPRq:
          execValid = true ->
          instVToPRqValid = true ->
          execData (ExecT !! wbEpoch) = wbEpochI ->
          instVToPRqData (InstVToPRqT !! wbEpoch) = wbEpochI ;

        regRead_fetchRp:
          regReadValid = true ->
          fetchRpValid = true ->
          regReadData (RegReadT !! wbEpoch) = wbEpochI ->
          fetchRpData (FetchRpT !! wbEpoch) = wbEpochI ;
          
        regRead_fetchRq:
          regReadValid = true ->
          fetchRqValid = true ->
          regReadData (RegReadT !! wbEpoch) = wbEpochI ->
          fetchRqData (FetchRqT !! wbEpoch) = wbEpochI ;

        regRead_instVToPRq:
          regReadValid = true ->
          instVToPRqValid = true ->
          regReadData (RegReadT !! wbEpoch) = wbEpochI ->
          instVToPRqData (InstVToPRqT !! wbEpoch) = wbEpochI ;

        fetchRp_fetchRq:
          fetchRpValid = true ->
          fetchRqValid = true ->
          fetchRpData (FetchRpT !! wbEpoch) = wbEpochI ->
          fetchRqData (FetchRqT !! wbEpoch) = wbEpochI ;
          
        fetchRp_instVToPRq:
          fetchRpValid = true ->
          instVToPRqValid = true ->
          fetchRpData (FetchRpT !! wbEpoch) = wbEpochI ->
          instVToPRqData (InstVToPRqT !! wbEpoch) = wbEpochI ;
          
        fetchRq_instVToPRq:
          fetchRqValid = true ->
          instVToPRqValid = true ->
          fetchRqData (FetchRqT !! wbEpoch) = wbEpochI ->
          instVToPRqData (InstVToPRqT !! wbEpoch) = wbEpochI ;
          
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

    Lemma notLongLatRewrite pc inst src1 src2:
      evalExpr (isNotLongLat _ inst) = true ->
      evalExpr (execFnNotLongLat _ pc inst src1 src2) =
      evalExpr (execFn _ pc inst src1 src2).
    Proof.
      intros.
      unfold execFn; simpl.
      rewrite H; reflexivity.
    Qed.

    Lemma longLatRewrite pc inst src1 src2:
      evalExpr (isNotLongLat _ inst) = false ->
      evalExpr (execFnLongLat _ pc inst src1 src2) =
      evalExpr (execFn _ pc inst src1 src2).
    Proof.
      intros.
      unfold execFn; simpl.
      rewrite H; reflexivity.
    Qed.

    Lemma execFnRewrite ty pc inst src1 src2:
      execFn ty pc inst src1 src2 =
      (IF isNotLongLat _ inst
       then execFnNotLongLat _ pc inst src1 src2
       else execFnLongLat _ pc inst src1 src2)%kami_expr.
    Proof.
      reflexivity.
    Qed.
    
    Opaque execFn.

    Lemma longLatFinish_inv:
      ruleMapInst combined_inv procInlUnfold procSpec longLatFinish.
    Proof.
      (* SKIP_PROOF_ON
      initInvRight procSpec "staleMemVAddr"%string.
      - unfold indexIn.
        cbv [evalExpr].
        rewrite (rmNonePartition 1).
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
      - let X := fresh in intros X; simpl in X; discriminate.
      - let X := fresh in intros X; simpl in X; discriminate.
      - let X := fresh in intros X; simpl in X; discriminate.
      - intros; simplBoolFalse; repeat substFind.
        unfold rfFromExecT, rfFromMemRqT, VectorFacts.Vector_find in *; simpl in *.
        rewrite ?andb_false_r, ?andb_false_l, ?orb_false_r, ?orb_false_l in *.
        intros; subst.
        auto.
      - intros; simplBoolFalse; repeat substFind; subst.
        unfold rfFromExecT, rfFromMemRqT, VectorFacts.Vector_find in *; simpl in *.
        rewrite ?andb_false_r, ?andb_false_l, ?orb_false_r, ?orb_false_l in *.
        intros; subst.
        specialize (regReadSrc1 eq_refl eq_refl).
        specialize (regReadSrc2 eq_refl eq_refl).
        repeat match goal with
               | H: context [?f (SyntaxKind Bool) ?e eq_refl] |- _ =>
                 replace f with Kami.SymEval.semExpr in H by reflexivity;
                   rewrite <- ?Kami.SymEval.semExpr_sound in H;
                   simpl in H
               end.
        simplBoolFalse.
        rewrite ?(longLatRewrite _ _ _ _ H8).
        match type of regReadSrc1 with
        | ?P = _ -> _ => case_eq P; intros
        end; match type of regReadSrc2 with
             | ?P = _ -> _ => case_eq P; intros
             end.
        + specialize (regReadSrc1 H0).
          specialize (regReadSrc2 H1).
          repeat f_equal; auto.
        + specialize (regReadSrc1 H0).
          erewrite  useSrc2Means.
          repeat f_equal; eauto.
          auto.
        + specialize (regReadSrc2 H1).
          erewrite useSrc1Means.
          repeat f_equal; eauto.
          auto.
        + erewrite useSrc1Means.
          erewrite useSrc2Means.
          repeat f_equal; eauto.
          auto.
          auto.
      - simplBoolFalse; repeat substFind.
        setoid_rewrite (rmNonePartition 1) at 3.
        cbv [partition fst snd].
        rewrite (rmNonePartition 0).
        cbv [partition fst snd].
        setoid_rewrite (rmNonePartition 0) at 2.
        cbv [partition fst snd].
        setoid_rewrite (rmNonePartition 0) at 3.
        cbv [partition fst snd].
        rewrite evalFalse; rmNoneNilLtac.
        setoid_rewrite (rmNonePartition 0) at 6.
        cbv [partition fst snd].
        unfold fromRegReadT.
        unfold rmNone at 6.
        unfold app at 4.
        setoid_rewrite nth_upd_length.
        unfold fromExecT at 1.
        unfold rmNone at 2, evalExpr at 1, evalConstT at 1.
        unfold app at 2.
        setoid_rewrite (rmNonePartition 0) at 3.
        cbv [partition fst snd].
        rmNoneNilLtac.
        (* Arguments rmNone A ls: simpl never. *)
        simpl.
        unfold updMemVAddr; simpl.
        repeat f_equal.
        unfold VectorFacts.Vector_find; simpl.
        reflexivity.
      - intros; simpl in *; discriminate.
      - intros; simpl in *; discriminate.
      - intros; simpl in *; discriminate.
      - intros; simpl in *; discriminate.
      - intros; simpl in *; discriminate.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Lemma longLatStart_inv:
      ruleMapInst combined_inv procInlUnfold procSpec longLatStart.
    Proof.
      (* SKIP_PROOF_ON
      simplInv; left;
        simplInvHyp;
      esplit; try simplMapUpds;
        try (reflexivity || eassumption);
        intros; simplBoolFalse; repeat substFind; auto.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.
    
    Lemma longLatDrop_inv:
      ruleMapInst combined_inv procInlUnfold procSpec longLatDrop.
    Proof.
      (* SKIP_PROOF_ON
      initInvRight procSpec "drop"%string;
        try solve [let X := fresh in intros X; simpl in X; discriminate]; simplBoolFalse;
          repeat substFind.
      rewrite evalFalse.
      unfold fromRegReadT.
      rewrite (rmNonePartition 1) at 1.
      setoid_rewrite (rmNonePartition 1) at 3.
      cbv [partition fst snd].
      setoid_rewrite (rmNonePartition 0) at 4.
      cbv [partition fst snd].
      unfold rmNone at 4.
      unfold app at 3.
      erewrite rmList_app.
      repeat f_equal.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Lemma instVToPRq_inv:
      ruleMapInst combined_inv procInlUnfold procSpec instVToPRq.
    Proof.
      (* SKIP_PROOF_ON
      initInvRight procSpec "stalePc"%string.
      rewrite (rmNonePartition 4).
      cbv [partition fst snd].
      simplBoolFalse.
      f_equal.
      instantiate (1 := regV).
      reflexivity.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Lemma wb_inv:
      ruleMapInst combined_inv procInlUnfold procSpec wb.
    Proof.
      (* SKIP_PROOF_ON
      simplInv; left;
        simplInvHyp;
        simplInvGoal; intros.
      - specialize (regReadSrc1 H H0 H1).
        unfold VectorFacts.Vector_find in *; simpl in *.
        rewrite regReadSrc1; repeat f_equal.
        extensionality x.
        destruct (weq x (memRpData Fin.F1)); auto.
      - specialize (regReadSrc2 H H0 H1).
        unfold VectorFacts.Vector_find in *; simpl in *.
        rewrite regReadSrc2; repeat f_equal; clear.
        extensionality x.
        destruct (weq x (memRpData Fin.F1)); auto.
      - specialize (execVal H).
        clear staleListFind.
        repeat substFind;
        subst;
        unfold rfFromMemRqT, VectorFacts.Vector_find in *; simpl in *.
        specialize (execVal eq_refl).
        repeat match goal with
               | |- context [if ?p then _ else _] => destruct p
               end; try (reflexivity || assumption).
      - specialize (memRqVal H).
        repeat substFind;
        subst;
        unfold rfFromMemRqT, VectorFacts.Vector_find in *; simpl in *.
        specialize (memRqVal eq_refl).
        repeat match goal with
               | |- context [if ?p then _ else _] => destruct p
               end; try (reflexivity || assumption).
      - clear - regFileSFind.
        unfold VectorFacts.Vector_find in *; simpl in *.
        rewrite regFileSFind; repeat f_equal; clear.
        extensionality x.
        destruct (weq x (memRpData Fin.F1)); auto.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Lemma fetchRq_inv:
      ruleMapInst combined_inv procInlUnfold procSpec fetchRq.
    Proof.
      (* SKIP_PROOF_ON
      initInvRight procSpec "staleInstVToP"%string.
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
      - setoid_rewrite (rmNonePartition 4) at 2.
        cbv [partition fst snd].
        unfold rmNone at 3.
        unfold fromInstVToPRqT.
        rewrite nth_len.
        reflexivity.
      - simplBoolFalse.
        rewrite (rmNonePartition 3) in staleListFind.
        setoid_rewrite (rmNonePartition 3) at 2.
        setoid_rewrite (rmNonePartition 3) at 4.
        rewrite (rmNonePartition 4) at 1.
        cbv [partition fst snd] in *.
        unfold evalExpr at 3.
        unfold evalConstT, fromInstVToPRqT.
        unfold fromFetchRqT at 2.
        unfold fromFetchRqT at 2.
        unfold rmNone at 6.
        rmNoneNilLtac.
        rewrite nth_upd_length.
        rewrite (rmNonePartition 3).
        cbv [partition fst snd].
        f_equal.
      - intros; simpl in *; discriminate.
      - intros; simpl in *; discriminate.
      - intros; simpl in *; discriminate.
      - intros; simpl in *; discriminate.
      - intros; simpl in *; discriminate.
        END_SKIP_PROOF_ON *) apply cheat.        
    Qed.

    Lemma fetchRp_inv:
      ruleMapInst combined_inv procInlUnfold procSpec fetchRp.
    Proof.
      (* SKIP_PROOF_ON
      initInvRight procSpec "staleInst"%string.
      - unfold indexIn.
        cbv [evalExpr].
        rewrite (rmNonePartition 3).
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
      - setoid_rewrite (rmNonePartition 3) at 2.
        cbv [partition fst snd].
        unfold rmNone at 3.
        unfold fromFetchRqT.
        rewrite nth_len.
        reflexivity.
      - simplBoolFalse.
        rewrite (rmNonePartition 2) in staleListFind.
        setoid_rewrite (rmNonePartition 2) at 2.
        setoid_rewrite (rmNonePartition 2) at 4.
        rewrite (rmNonePartition 3) at 1.
        cbv [partition fst snd] in *.
        unfold evalExpr at 3.
        unfold evalConstT, fromFetchRqT.
        unfold fromFetchRpT at 2.
        unfold fromFetchRpT at 2.
        unfold rmNone at 6.
        rmNoneNilLtac.
        rewrite nth_upd_length.
        rewrite (rmNonePartition 2).
        cbv [partition fst snd].
        unfold rmNone at 3.
        rewrite <- app_assoc.
        f_equal.
      - intros; simpl in *; discriminate.
      - intros; simpl in *; discriminate.
      - intros; simpl in *; discriminate.
      - intros; simpl in *; discriminate.
      - intros; simpl in *; discriminate.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Lemma exec_inv:
      ruleMapInst combined_inv procInlUnfold procSpec exec.
    Proof.
      (* SKIP_PROOF_ON
      initInvRight procSpec "staleMemVAddr"%string.
      - unfold indexIn.
        cbv [evalExpr].
        rewrite (rmNonePartition 1).
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
      - let X := fresh in intros X; simpl in X; discriminate.
      - let X := fresh in intros X; simpl in X; discriminate.
      - let X := fresh in intros X; simpl in X; discriminate.
      - intros; simplBoolFalse; repeat substFind.
        unfold rfFromExecT, rfFromMemRqT, VectorFacts.Vector_find in *; simpl in *.
        rewrite ?andb_false_r, ?andb_false_l, ?orb_false_r, ?orb_false_l in *.
        auto.
      - intros; simplBoolFalse; repeat substFind; subst.
        unfold rfFromExecT, rfFromMemRqT, VectorFacts.Vector_find in *; simpl in *.
        rewrite ?andb_false_r, ?andb_false_l, ?orb_false_r, ?orb_false_l in *.
        intros; subst.
        specialize (regReadSrc1 eq_refl eq_refl).
        specialize (regReadSrc2 eq_refl eq_refl).
        repeat match goal with
               | H: context [?f (SyntaxKind Bool) ?e eq_refl] |- _ =>
                 replace f with Kami.SymEval.semExpr in H by reflexivity;
                   rewrite <- ?Kami.SymEval.semExpr_sound in H;
                   simpl in H
               end.
        rewrite (notLongLatRewrite _ _ _ _ H5).
        match type of regReadSrc1 with
        | ?P = _ -> _ => case_eq P; intros
        end; match type of regReadSrc2 with
             | ?P = _ -> _ => case_eq P; intros
             end.
        + specialize (regReadSrc1 H0).
          specialize (regReadSrc2 H1).
          repeat f_equal; auto.
        + specialize (regReadSrc1 H0).
          erewrite  useSrc2Means.
          repeat f_equal; eauto.
          auto.
        + specialize (regReadSrc2 H1).
          erewrite useSrc1Means.
          repeat f_equal; eauto.
          auto.
        + erewrite useSrc1Means.
          erewrite useSrc2Means.
          repeat f_equal; eauto.
          auto.
          auto.
      - simplBoolFalse; repeat substFind.
        setoid_rewrite (rmNonePartition 1) at 3.
        cbv [partition fst snd].
        rewrite (rmNonePartition 0).
        cbv [partition fst snd].
        setoid_rewrite (rmNonePartition 0) at 2.
        cbv [partition fst snd].
        setoid_rewrite (rmNonePartition 0) at 3.
        cbv [partition fst snd].
        rewrite evalFalse; rmNoneNilLtac.
        setoid_rewrite (rmNonePartition 0) at 6.
        cbv [partition fst snd].
        unfold fromRegReadT.
        unfold rmNone at 6.
        unfold app at 4.
        setoid_rewrite nth_upd_length.
        unfold fromExecT at 1.
        unfold rmNone at 2, evalExpr at 1, evalConstT at 1.
        unfold app at 2.
        setoid_rewrite (rmNonePartition 0) at 3.
        cbv [partition fst snd].
        rmNoneNilLtac.
        simpl.
        unfold updMemVAddr; simpl.
        repeat f_equal.
        unfold VectorFacts.Vector_find; simpl.
        reflexivity.
      - intros; simpl in *; discriminate.
      - intros; simpl in *; discriminate.
      - intros; simpl in *; discriminate.
      - intros; simpl in *; discriminate.
      - intros; simpl in *; discriminate.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Lemma regRead_inv:
      ruleMapInst combined_inv procInlUnfold procSpec regRead.
    Proof.
      (* SKIP_PROOF_ON
      simplInv; left;
        simplInvHyp;
      esplit; try simplMapUpds;
        try (reflexivity || eassumption);
        intros; simplBoolFalse; repeat substFind; auto.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Lemma memVToPRq_inv:
      ruleMapInst combined_inv procInlUnfold procSpec memVToPRq.
    Proof.
      (* SKIP_PROOF_ON
      initInvRight procSpec "staleMemVToP"%string;
        try solve [let X := fresh in intros X; simpl in X; discriminate].
      - simplBoolFalse; repeat substFind.
        rewrite (rmNonePartition 0).
        cbv [partition fst snd].
        unfold fromMemRqT; unfold rmNone at 1.
        rewrite ?app_nil_l.
        rewrite (rmNonePartition 0).
        cbv [partition fst snd].
        unfold fromExecT; unfold rmNone at 1, app.
        instantiate (1 := 0).
        reflexivity.
      - simplBoolFalse; repeat substFind.
        rewrite (rmNonePartition 0).
        cbv [partition fst snd].
        unfold fromMemRqT; unfold rmNone at 1.
        rewrite ?app_nil_l.
        rewrite (rmNonePartition 0).
        cbv [partition fst snd].
        unfold fromExecT; unfold rmNone at 1, app.
        reflexivity.
      - simplBoolFalse; repeat substFind.
        unfold rfFromExecT, rfFromMemRqT, VectorFacts.Vector_find in *; simpl in *.
        progress rewrite ?andb_false_r, ?andb_false_l, ?orb_false_r, ?orb_false_l in *.
        intros; repeat f_equal; auto.
      - simplBoolFalse; repeat substFind.
        unfold rfFromExecT, rfFromMemRqT, VectorFacts.Vector_find in *; simpl in *.
        progress rewrite ?andb_false_r, ?andb_false_l, ?orb_false_r, ?orb_false_l in *.
        intros; repeat f_equal; auto.
      - simplBoolFalse; repeat substFind.
        unfold rfFromExecT, rfFromMemRqT, VectorFacts.Vector_find in *; simpl in *.
        progress rewrite ?andb_false_r, ?andb_false_l, ?orb_false_r, ?orb_false_l in *.
        intros; repeat f_equal; auto.
      - simplBoolFalse; repeat substFind.
        unfold rfFromExecT, rfFromMemRqT, VectorFacts.Vector_find in *; simpl in *.
        progress rewrite ?andb_false_r, ?andb_false_l, ?orb_false_r, ?orb_false_l in *.
        intros; repeat f_equal; auto.
      - simplBoolFalse; repeat substFind.
        unfold rfFromExecT, rfFromMemRqT, VectorFacts.Vector_find in *; simpl in *.
        progress rewrite ?andb_false_r, ?andb_false_l, ?orb_false_r, ?orb_false_l in *.
        intros; repeat f_equal; auto.
      - simplBoolFalse; repeat substFind.
        unfold fromMemRqT, fromExecT.
        rewrite evalFalse.
        setoid_rewrite (rmNonePartition 0) at 2.
        cbv [partition fst snd].
        rmNoneNilLtac.
        setoid_rewrite (rmNonePartition 0) at 2.
        cbv [partition fst snd].        
        unfold rmNone at 2.
        unfold app.
        unfold nth_upd.
        setoid_rewrite (rmNonePartition 0) at 1.
        cbv [partition fst snd].        
        unfold evalExpr at 1, evalConstT at 1, rmNone at 1.
        unfold app at 1.
        setoid_rewrite (rmNonePartition 0) at 1.
        cbv [partition fst snd].        
        rmNoneNilLtac.
        f_equal.
        END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Lemma memVToPRqNone_inv:
      ruleMapInst combined_inv procInlUnfold procSpec memVToPRqNone.
    Proof.
      (* SKIP_PROOF_ON
      simplInv; left;
        simplInvHyp;
      esplit; try simplMapUpds;
        try (reflexivity || eassumption);
        intros; simplBoolFalse; repeat substFind; auto.
      - simplBoolFalse; repeat substFind.
        unfold rfFromExecT, rfFromMemRqT, VectorFacts.Vector_find in *; simpl in *.
        progress rewrite ?andb_false_r, ?andb_false_l, ?orb_false_r, ?orb_false_l in *.
        intros; repeat f_equal; auto.
      - simplBoolFalse; repeat substFind.
        unfold rfFromExecT, rfFromMemRqT, VectorFacts.Vector_find in *; simpl in *.
        progress rewrite ?andb_false_r, ?andb_false_l, ?orb_false_r, ?orb_false_l in *.
        intros; repeat f_equal; auto.
      - simplBoolFalse; repeat substFind.
        unfold rfFromExecT, rfFromMemRqT, VectorFacts.Vector_find in *; simpl in *.
        progress rewrite ?andb_false_r, ?andb_false_l, ?orb_false_r, ?orb_false_l in *.
        intros; repeat f_equal; auto.
      - discriminate.
      - discriminate.
      - simplBoolFalse; repeat substFind.
        unfold rfFromExecT, rfFromMemRqT, VectorFacts.Vector_find in *; simpl in *.
        progress rewrite ?andb_false_r, ?andb_false_l, ?orb_false_r, ?orb_false_l in *.
        intros; repeat f_equal; auto.
      - simpl.
        repeat match goal with
               | H: context [?f (SyntaxKind Bool) ?e eq_refl] |- _ =>
                 replace f with Kami.SymEval.semExpr in H by reflexivity;
                   rewrite <- ?Kami.SymEval.semExpr_sound in H;
                   simpl in H
               end.
        simpl in H0.
        rewrite orb_true_iff in H0.
        contradiction.
        END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Lemma regReadDrop_inv:
      ruleMapInst combined_inv procInlUnfold procSpec regReadDrop.
    Proof.
      (* SKIP_PROOF_ON
      initInvRight procSpec "drop"%string;
        try solve [let X := fresh in intros X; simpl in X; discriminate]; simplBoolFalse;
          repeat substFind.
      rewrite evalFalse.
      unfold fromFetchRpT.
      rewrite (rmNonePartition 2) at 1.
      setoid_rewrite (rmNonePartition 2) at 3.
      cbv [partition fst snd].
      setoid_rewrite (rmNonePartition 0) at 4.
      cbv [partition fst snd].
      unfold rmNone at 4.
      unfold app at 3.
      erewrite rmList_app.
      repeat f_equal.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Lemma memRqDrop_inv:
      ruleMapInst combined_inv procInlUnfold procSpec memRqDrop.
    Proof.
      (* SKIP_PROOF_ON
      initInvRight procSpec "drop"%string;
        try solve [let X := fresh in intros X; simpl in X; discriminate]; simplBoolFalse;
          repeat substFind.
      - simpl in H6.
        fold (negb (memRqData Fin.F1)) in H6.
        subst.
        
        unfold rfFromExecT, rfFromMemRqT, VectorFacts.Vector_find in *; simpl in *.
        destruct (memRqData Fin.F1); simpl in *;
          progress rewrite ?andb_false_r, ?andb_false_l, ?orb_false_r, ?orb_false_l in *;
          repeat f_equal; auto.
      - simpl in H6.
        fold (negb (memRqData Fin.F1)) in H6.
        subst.
        
        unfold rfFromExecT, rfFromMemRqT, VectorFacts.Vector_find in *; simpl in *.
        destruct (memRqData Fin.F1); simpl in *;
          progress rewrite ?andb_false_r, ?andb_false_l, ?orb_false_r, ?orb_false_l in *;
          repeat f_equal; auto.
      - simpl in H6.
        fold (negb (memRqData Fin.F1)) in H6.
        subst.
        
        unfold rfFromExecT, rfFromMemRqT, VectorFacts.Vector_find in *; simpl in *.
        destruct (memRqData Fin.F1); simpl in *;
          progress rewrite ?andb_false_r, ?andb_false_l, ?orb_false_r, ?orb_false_l in *;
          repeat f_equal; auto.
      - simpl in H6.
        fold (negb (memRqData Fin.F1)) in H6.
        subst.
        
        unfold rfFromExecT, rfFromMemRqT, VectorFacts.Vector_find in *; simpl in *.
        destruct (memRqData Fin.F1); simpl in *;
          progress rewrite ?andb_false_r, ?andb_false_l, ?orb_false_r, ?orb_false_l in *;
          repeat f_equal; auto.
      - simpl in H6.
        fold (negb (memRqData Fin.F1)) in H6.
        subst.
        
        unfold rfFromExecT, rfFromMemRqT, VectorFacts.Vector_find in *; simpl in *.
        destruct (memRqData Fin.F1); simpl in *;
          progress rewrite ?andb_false_r, ?andb_false_l, ?orb_false_r, ?orb_false_l in *;
          repeat f_equal; auto.
      - rewrite evalFalse; unfold fromMemRqT.
        instantiate (1 := 0); simpl; reflexivity.
      END_SKIP_PROOF_ON *) apply cheat.

    Qed.

    Lemma execDrop_inv:
      ruleMapInst combined_inv procInlUnfold procSpec execDrop.
    Proof.
      (* SKIP_PROOF_ON
      initInvRight procSpec "drop"%string;
        try solve [let X := fresh in intros X; simpl in X; discriminate]; simplBoolFalse;
          repeat substFind.
      rewrite evalFalse.
      unfold fromRegReadT.
      rewrite (rmNonePartition 1) at 1.
      setoid_rewrite (rmNonePartition 1) at 3.
      cbv [partition fst snd].
      setoid_rewrite (rmNonePartition 0) at 4.
      cbv [partition fst snd].
      unfold rmNone at 4.
      unfold app at 3.
      erewrite rmList_app.
      repeat f_equal.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Lemma memRq_inv:
      ruleMapInst combined_inv procInlUnfold procSpec memRq.
    Proof.
      (* SKIP_PROOF_ON
      initInvRight procSpec "memRq"%string;
        try solve [let X := fresh in intros X; simpl in X; discriminate]; simplBoolFalse;
          repeat substFind.
      - simpl.
        rewrite orb_true_r.
        reflexivity.
      - simpl.
        clear - nonMemVToPRpLdSt.
        unfold VectorFacts.Vector_find in *; simpl in *.
        match goal with
        | |- negb ?x || _ = true =>
          destruct x; simpl; auto
        end.
      - simpl.
        rewrite ?andb_false_l, ?andb_false_r in memRqVal.
        simpl in H8.
        rewrite <- (memRqVal eq_refl (eq_sym H8)).
        match goal with
          | |- context[if ?p then _ else _] => destruct p; try (reflexivity || tauto)
        end.
        rewrite orb_true_r.
        reflexivity.
      - try reflexivity;
          apply M.elements_eq_leibniz;
          try reflexivity;
          meqReify_eq_tac.
        do 2 f_equal.
        
        unfold andb in *; simpl in *; rewrite <- (memRqVal eq_refl (eq_sym H8)).
        reflexivity.
      - simpl.
        simpl in H9.
        subst.
        match goal with
        | |- (if ?p then _ else _) = _ => destruct p; tauto
        end.
      - meqReify.
      - meqReify.
      - clear staleListFind.
        unfold rfFromExecT, rfFromMemRqT in *.
        simpl in *;
          repeat rewrite ?andb_false_l, ?andb_true_l, ?andb_false_r, ?andb_true_r in *;
          simpl in *.
        intros;
          subst;
          specialize (regReadSrc1 eq_refl);
          specialize (regReadSrc2 eq_refl);
          specialize (memRq_regRead eq_refl eq_refl eq_refl);
          specialize (regReadNoStall eq_refl).
        match type of H0 with
        | _ = if ?P then _ else _ => destruct P
        end.
        + rewrite H0 in memRq_regRead.
          apply no_fixpoint_negb in memRq_regRead; contradiction.
        + specialize (regReadSrc1 memRq_regRead H1).
          simpl.
          unfold VectorFacts.Vector_find in *; simpl in *.
          rewrite ?rewriteBoolDec in *.
          simpl in regReadSrc1.
          simpl in regReadNoStall.
          match goal with
          | |- _ = if ?P then _ else _ => destruct P; [assumption|]
          end.
          rewrite orb_false_iff in regReadNoStall;
            destruct regReadNoStall as [rs1 rs2].
          unfold andb; simpl in *.
          rewrite H1 in *.
          repeat match goal with
                 | |- context[if if ?P then _ else _ then _ else _] => destruct P
                 | |- context[if ?P then _ else _] => destruct P
                 end; simpl in *;
            repeat rewrite ?andb_false_l, ?andb_true_l, ?andb_false_r, ?andb_true_r in *;
            try discriminate; auto.
      - clear staleListFind.
        unfold rfFromExecT, rfFromMemRqT in *.
        simpl in *;
          repeat rewrite ?andb_false_l, ?andb_true_l, ?andb_false_r, ?andb_true_r in *;
          simpl in *.
        intros;
          subst;
          specialize (regReadSrc1 eq_refl);
          specialize (regReadSrc2 eq_refl);
          specialize (memRq_regRead eq_refl eq_refl eq_refl);
          specialize (regReadNoStall eq_refl).
        match type of H0 with
        | _ = if ?P then _ else _ => destruct P
        end.
        + rewrite H0 in memRq_regRead.
          apply no_fixpoint_negb in memRq_regRead; contradiction.
        + specialize (regReadSrc2 memRq_regRead H1).
          simpl.
          unfold VectorFacts.Vector_find in *; simpl in *.
          rewrite ?rewriteBoolDec in *.
          simpl in regReadSrc2.
          simpl in regReadNoStall.
          match goal with
          | |- _ = if ?P then _ else _ => destruct P; [assumption|]
          end.
          rewrite orb_false_iff in regReadNoStall;
            destruct regReadNoStall as [rs1 rs2].
          unfold andb; simpl in *.
          rewrite H1 in *.
          repeat match goal with
                 | |- context[if if ?P then _ else _ then _ else _] => destruct P
                 | |- context[if ?P then _ else _] => destruct P
                 end; simpl in *;
            repeat rewrite ?andb_false_l, ?andb_true_l, ?andb_false_r, ?andb_true_r in *;
            try discriminate; auto.
          simpl in rs2.
          rewrite orb_true_r in *.
          discriminate.
      - clear staleListFind; repeat substFind; subst.
        repeat rewrite ?andb_false_l, ?andb_true_l, ?andb_false_r, ?andb_true_r in *.
        simpl in *.
        intros X; specialize (regReadNoStall X).
        unfold rfFromExecT, rfFromMemRqT in *.
        rewrite orb_false_iff in regReadNoStall.
        dest.
        rewrite orb_false_r.
        subst.
        match goal with
          | |- context[if bool_dec ?x ?y then _ else _] => destruct (bool_dec x y)
        end;
          repeat rewrite ?andb_false_l, ?andb_true_l, ?andb_false_r, ?andb_true_r in *;
          subst; auto.
        match type of H with
          | context[if bool_dec ?a ?b then _ else _] => destruct (bool_dec a b)
        end;
          repeat rewrite ?andb_false_l, ?andb_true_l, ?andb_false_r, ?andb_true_r in *;
          subst; auto.
        destruct execValid.
        + specialize (memRq_exec eq_refl eq_refl eq_refl).
          congruence.
        + repeat rewrite ?andb_false_l, ?andb_true_l, ?andb_false_r, ?andb_true_r in *.
          reflexivity.
      - simpl; repeat rewrite ?andb_false_l, ?andb_true_l, ?andb_false_r, ?andb_true_r in *.
        auto.
      - simpl.
        intros.
        subst.
        unfold rfFromMemRqT in *; simpl.
        match type of H0 with
        | context[if ?P then _ else _] => destruct P
        end.
        + unfold negb; simpl.
          specialize (memRq_exec eq_refl eq_refl (eq_sym H8)).
          rewrite memRq_exec in H0.
          clear - H0; destruct wbEpochI; discriminate.
        + specialize (execVal eq_refl H0).
          simpl in memRqVal.
          clear staleListFind.
          simpl in H8; apply eq_sym in H8.
          subst.
          repeat rewrite ?andb_false_l, ?andb_true_l, ?andb_false_r, ?andb_true_r in *.
          simpl in *.
          rewrite rewriteBoolDec in *.
          repeat rewrite ?andb_false_l, ?andb_true_l, ?andb_false_r, ?andb_true_r in *.
          specialize (execNoStall eq_refl).
          repeat (rewrite ?andb_false_iff, ?orb_false_iff in execNoStall).
          dest.
          unfold VectorFacts.Vector_find in *; simpl in *.
          repeat (destruct execNoStall as [execNoStall | execNoStall];
                  dest;
                  repeat rewrite ?andb_false_l, ?andb_true_l, ?andb_false_r, ?andb_true_r in *;
                  rewrite ?execNoStall in *; simpl in *; auto).
          * repeat rewrite ?andb_false_l, ?andb_true_l, ?andb_false_r, ?andb_true_r in *.
            auto.
          * { destruct H, H1.
              - specialize (useSrc1Means (execData (ExecT !! pc)) _ H).
                specialize (useSrc2Means (execData (ExecT !! pc)) _ H1).
                rewrite execVal.
                erewrite useSrc1Means.
                erewrite useSrc2Means.
                reflexivity.
              - specialize (useSrc1Means (execData (ExecT !! pc)) _ H).
                rewrite execVal.
                erewrite useSrc1Means.
                rewrite H1.
                rewrite H1 in execVal.
                simpl; simpl in execVal.
                repeat rewrite ?andb_false_l, ?andb_true_l, ?andb_false_r, ?andb_true_r in *.
                reflexivity.
              - specialize (useSrc2Means (execData (ExecT !! pc)) _ H1).
                rewrite execVal.
                erewrite useSrc2Means.
                rewrite H.
                rewrite H in execVal.
                simpl; simpl in execVal.
                repeat rewrite ?andb_false_l, ?andb_true_l, ?andb_false_r, ?andb_true_r in *.
                reflexivity.
              - rewrite execVal.
                rewrite H1, H.
                rewrite H1, H in execVal.
                simpl; simpl in execVal.
                repeat rewrite ?andb_false_l, ?andb_true_l, ?andb_false_r, ?andb_true_r in *.
                reflexivity.
            }
      - simpl.
        simpl in memRqVal.
        rewrite <- ?(memRqVal eq_refl (eq_sym H8)).
        repeat f_equal.
        extensionality x.
        simpl.
        unfold VectorFacts.Vector_find.
        simpl.
        repeat match goal with
               | |- context[if ?P then _ else _] => destruct P; simpl
               end; reflexivity.
      - simpl.
        match goal with
        | |- context [if ?P then _ else _] => destruct P; [| assumption]
        end.
        intros.
        simpl in H8.
        specialize (memRq_exec eq_refl H).
        specialize (memRq_regRead eq_refl H0).
        subst.
        specialize (memRq_exec eq_refl).
        specialize (memRq_regRead eq_refl).
        rewrite H1 in *.
        apply no_fixpoint_negb in memRq_exec.
        contradiction.
      - simpl.
        match goal with
        | |- context [if ?P then _ else _] => destruct P; [| assumption]
        end.
        intros.
        simpl in H8.
        specialize (memRq_exec eq_refl H).
        specialize (memRq_fetchRp eq_refl H0).
        subst.
        specialize (memRq_exec eq_refl).
        specialize (memRq_fetchRp eq_refl).
        rewrite H1 in *.
        apply no_fixpoint_negb in memRq_exec.
        contradiction.
      - simpl.
        match goal with
        | |- context [if ?P then _ else _] => destruct P; [| assumption]
        end.
        intros.
        simpl in H8.
        specialize (memRq_exec eq_refl H).
        specialize (memRq_fetchRq eq_refl H0).
        subst.
        specialize (memRq_exec eq_refl).
        specialize (memRq_fetchRq eq_refl).
        rewrite H1 in *.
        apply no_fixpoint_negb in memRq_exec.
        contradiction.
      - simpl.
        match goal with
        | |- context [if ?P then _ else _] => destruct P; [| assumption]
        end.
        intros.
        simpl in H8.
        specialize (memRq_exec eq_refl H).
        specialize (memRq_instVToPRq eq_refl H0).
        subst.
        specialize (memRq_exec eq_refl).
        specialize (memRq_instVToPRq eq_refl).
        rewrite H1 in *.
        apply no_fixpoint_negb in memRq_exec.
        contradiction.
      - simpl.
        match goal with
        | |- context [if ?P then _ else _] => destruct P; [| assumption]
        end.
        intros.
        simpl in H8.
        specialize (memRq_regRead eq_refl H).
        specialize (memRq_fetchRp eq_refl H0).
        subst.
        specialize (memRq_regRead eq_refl).
        specialize (memRq_fetchRp eq_refl).
        rewrite H1 in *.
        apply no_fixpoint_negb in memRq_regRead.
        contradiction.
      - simpl.
        match goal with
        | |- context [if ?P then _ else _] => destruct P; [| assumption]
        end.
        intros.
        simpl in H8.
        specialize (memRq_regRead eq_refl H).
        specialize (memRq_fetchRq eq_refl H0).
        subst.
        specialize (memRq_regRead eq_refl).
        specialize (memRq_fetchRq eq_refl).
        rewrite H1 in *.
        apply no_fixpoint_negb in memRq_regRead.
        contradiction.
      - simpl.
        match goal with
        | |- context [if ?P then _ else _] => destruct P; [| assumption]
        end.
        intros.
        simpl in H8.
        specialize (memRq_regRead eq_refl H).
        specialize (memRq_instVToPRq eq_refl H0).
        subst.
        specialize (memRq_regRead eq_refl).
        specialize (memRq_instVToPRq eq_refl).
        rewrite H1 in *.
        apply no_fixpoint_negb in memRq_regRead.
        contradiction.
      - simpl.
        match goal with
        | |- context [if ?P then _ else _] => destruct P; [| assumption]
        end.
        intros.
        simpl in H8.
        specialize (memRq_fetchRp eq_refl H).
        specialize (memRq_fetchRq eq_refl H0).
        subst.
        specialize (memRq_fetchRp eq_refl).
        specialize (memRq_fetchRq eq_refl).
        rewrite H1 in *.
        apply no_fixpoint_negb in memRq_fetchRp.
        contradiction.
      - simpl.
        match goal with
        | |- context [if ?P then _ else _] => destruct P; [| assumption]
        end.
        intros.
        simpl in H8.
        specialize (memRq_fetchRp eq_refl H).
        specialize (memRq_instVToPRq eq_refl H0).
        subst.
        specialize (memRq_fetchRp eq_refl).
        specialize (memRq_instVToPRq eq_refl).
        rewrite H1 in *.
        apply no_fixpoint_negb in memRq_fetchRp.
        contradiction.
      - simpl.
        match goal with
        | |- context [if ?P then _ else _] => destruct P; [| assumption]
        end.
        intros.
        simpl in H8.
        specialize (memRq_fetchRq eq_refl H).
        specialize (memRq_instVToPRq eq_refl H0).
        subst.
        specialize (memRq_fetchRq eq_refl).
        specialize (memRq_instVToPRq eq_refl).
        rewrite H1 in *.
        apply no_fixpoint_negb in memRq_fetchRq.
        contradiction.
        END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Lemma procInlUnfold_refines_procSpec:
      procInlUnfold <<== procSpec.
    Proof.
      (* SKIP_PROOF_ON
      apply decompositionZeroR_Id_Rule with (thetaR := combined_inv).
      - simpl.
        esplit; simpl; intros; try (reflexivity || discriminate).
      - reflexivity.
      - reflexivity.
      - intros.
        simpl in H0.
        destruct H0. eapply instVToPRq_inv; eauto.
        destruct H0. eapply regRead_inv; eauto.
        destruct H0. eapply regReadDrop_inv; eauto.
        destruct H0. eapply exec_inv; eauto.
        destruct H0. eapply execDrop_inv; eauto.
        destruct H0. eapply wb_inv; eauto.
        destruct H0. eapply fetchRq_inv; eauto.
        destruct H0. eapply fetchRp_inv; eauto.
        destruct H0. eapply longLatStart_inv; eauto.
        destruct H0. eapply longLatFinish_inv; eauto.
        destruct H0. eapply longLatDrop_inv; eauto.
        destruct H0. eapply memVToPRq_inv; eauto.
        destruct H0. eapply memVToPRqNone_inv; eauto. 
        destruct H0. eapply memRq_inv; eauto.
        destruct H0. eapply memRqDrop_inv; eauto.
        contradiction.
        END_SKIP_PROOF_ON *) apply cheat.
    Qed.

    Lemma procFull_refines_procSpec:
      modFromMetaModules procFull <<== procSpec.
    Proof.
      (* SKIP_PROOF_ON
      fullTrans (modFromMeta procFullInl).
      - apply procFullInl_ref.
      - apply procInlUnfold_refines_procSpec.
      END_SKIP_PROOF_ON *) apply cheat.
    Qed.
  End Pf.
End Processor.

Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.MemTypes Ex.Fifo Ex.NativeFifo.
Require Import Fetch Decode RegRead Execute Mem Writeback AbstractIsa.

Set Implicit Arguments.

Open Scope string.

Section Processor.
  Variables addrSize dataBytes rfIdx: nat.

  Definition iMemReqName := "iMemReq".
  Definition iMemRepName := "iMemRep".
  Definition dMemReqName := "dMemReq".
  Definition dMemRepName := "dMemRep".

  Variable decodeInst: DecodeT dataBytes rfIdx.
  Variable execInst: ExecT addrSize dataBytes rfIdx.

  Definition f2dName := "f2d".
  Definition d2rName := "d2r".
  Definition r2eName := "r2e".
  Definition e2mName := "e2m".
  Definition m2wName := "m2w".
  Definition decName := "dec".
  Definition exeName := "dec".
  Definition bhtTrainName := "bhtTrain".

  Variables btbIndexSize btbTagSize bhtIndexSize bhtTrainSize: nat.
  Hypothesis (Hbtb: btbIndexSize + btbTagSize = addrSize).

  (** Fetch related *)
  Definition fetch := fetch addrSize dataBytes iMemReqName f2dName.
  Definition btb := btb btbIndexSize btbTagSize Hbtb.
  Definition decRedir := redirect addrSize decName.
  Definition exeRedir := redirect addrSize exeName.
  Definition decEpoch := epoch decName.
  Definition exeEpoch := epoch exeName.
  Definition f2d := @nativeFifo f2dName (Struct (F2D addrSize)) Default.

  (** Fetch related *)
  Definition decode := decode addrSize f2dName d2rName iMemRepName decodeInst.
  Definition bht := bht addrSize bhtIndexSize.
  Definition bhtTrain := fifo bhtTrainName bhtTrainSize (Struct (bhtUpdateStr addrSize)).
  Definition d2r := @nativeFifo d2rName (Struct (D2R addrSize dataBytes rfIdx)) Default.
  
  Definition regRead := regRead addrSize dataBytes rfIdx d2rName r2eName.
  Definition rf := regFile dataBytes rfIdx.
  Definition bypass := bypass dataBytes rfIdx.
  Definition r2e := @nativeFifo r2eName (Struct (R2E addrSize dataBytes rfIdx)) Default.
  
  Definition execute := execute r2eName e2mName bhtTrainName execInst.
  Definition e2m := @nativeFifo e2mName (Struct (E2M addrSize dataBytes rfIdx)) Default.
  
  Definition mem := mem addrSize dataBytes rfIdx e2mName m2wName dMemReqName.
  Definition m2w := @nativeFifo m2wName (Struct (M2W addrSize dataBytes rfIdx)) Default.
  
  Definition writeback := writeback addrSize dataBytes rfIdx m2wName dMemRepName.

  (* TODO: tohost (or DMA-based message passing) *)
  Definition inOrderSix :=
    (fetch ++ btb ++ decRedir ++ exeRedir ++ decEpoch ++ exeEpoch ++ f2d ++
           decode ++ bht ++ bhtTrain ++ d2r ++
           regRead ++ rf ++ bypass ++ r2e ++
           execute ++ e2m ++
           mem ++ m2w ++
           writeback)%kami.

End Processor.


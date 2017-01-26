Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.MemTypes Ex.OneEltFifo Ex.Fifo.
Require Import Fetch Decode RegRead Execute Mem Writeback AbstractIsa.

Set Implicit Arguments.

Open Scope string.

Section Processor.
  Variables addrSize dataBytes rfIdx: nat.
  Variables iMemReqName iMemRepName dMemReqName dMemRepName: string.

  Variable decodeInst: DecodeT dataBytes rfIdx.
  Variable execInst: ExecT addrSize dataBytes rfIdx.

  Definition f2dName := "f2d".
  Definition d2rName := "d2r".
  Definition r2eName := "r2e".
  Definition e2mName := "e2m".
  Definition m2wName := "m2w".
  Definition bhtTrainName := "bhtTrain".

  Variables btbIndexSize btbTagSize bhtIndexSize bhtTrainSize: nat.
  Hypothesis (Hbtb: btbIndexSize + btbTagSize = addrSize).

  Definition fetch := fetch addrSize dataBytes iMemReqName f2dName.
  Definition btb := btb btbIndexSize btbTagSize Hbtb.
  Definition decRedir := redirect addrSize "dec".
  Definition exeRedir := redirect addrSize "exe".
  Definition decEpoch := epoch "dec".
  Definition exeEpoch := epoch "exe".
  Definition f2d := oneEltFifo f2dName (Struct (F2D addrSize)).
  
  Definition decode := decode addrSize f2dName d2rName iMemRepName decodeInst.
  Definition bht := bht addrSize bhtIndexSize.
  Definition bhtTrain := fifo bhtTrainName bhtTrainSize (Struct (bhtUpdateStr addrSize)).
  Definition d2r := oneEltFifo d2rName (Struct (D2R addrSize dataBytes rfIdx)).
  
  Definition regRead := regRead addrSize dataBytes rfIdx d2rName r2eName.
  Definition rf := regFile dataBytes rfIdx.
  (* Definition scoreBoard := TODO. *)
  Definition r2e := oneEltFifo r2eName (Struct (R2E addrSize dataBytes rfIdx)).
  
  Definition execute := execute r2eName e2mName bhtTrainName execInst.
  Definition e2m := oneEltFifo e2mName (Struct (E2M addrSize dataBytes rfIdx)).
  
  Definition mem := mem addrSize dataBytes rfIdx e2mName m2wName dMemReqName.
  Definition m2w := oneEltFifo m2wName (Struct (M2W addrSize dataBytes rfIdx)).
  
  Definition writeback := writeback addrSize dataBytes rfIdx m2wName dMemRepName.

  (* TODO: scoreboard, tohost (or DMA-based message passing) *)
  Definition inOrderSix :=
    (fetch ++ btb ++ decRedir ++ exeRedir ++ decEpoch ++ exeEpoch ++ f2d ++
           decode ++ bht ++ bhtTrain ++ d2r ++
           regRead ++ rf ++ r2e ++
           execute ++ e2m ++
           mem ++ m2w ++
           writeback)%kami.
  
End Processor.


Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import Proc.AbstractIsa Proc.FetchBtb Proc.InOrderEightStage.

Set Implicit Arguments.
Open Scope string.

Section Processor.
  Variables addrSize dataBytes rfIdx: nat.
  Variables iExecName dExecName: string.

  Variable decodeInst: DecodeT dataBytes rfIdx.
  Variable execInst: ExecT addrSize dataBytes rfIdx.

  Variables btbIndexSize btbTagSize bhtIndexSize bhtTrainSize: nat.
  Hypothesis (Hbtb: btbIndexSize + btbTagSize = addrSize).

  (** Fetch related *)
  Definition decRedir := decRedir addrSize.
  Definition exeRedir := exeRedir addrSize.
  Definition f2i := f2i addrSize dataBytes.

  (** IMem related *)
  Definition iMem := iMem addrSize dataBytes iExecName.
  Definition i2d := i2d addrSize dataBytes.

  (** Decode related *)
  Definition decode := decode addrSize decodeInst.
  Definition bht := bht addrSize bhtIndexSize.
  Definition bhtTrain := bhtTrain addrSize bhtTrainSize.
  Definition d2r := d2r addrSize dataBytes rfIdx.

  (** RegRead related *)
  Definition regRead := regRead addrSize dataBytes rfIdx.
  Definition rf := rf dataBytes rfIdx.
  Definition bypass := bypass dataBytes rfIdx.
  Definition r2e := r2e addrSize dataBytes rfIdx.

  (** Execute related *)
  Definition execute := execute execInst.
  Definition e2m := e2m addrSize dataBytes rfIdx.

  (** Mem related *)
  Definition mem := mem addrSize dataBytes rfIdx.
  Definition m2d := m2d addrSize dataBytes rfIdx.

  (** DMem related *)
  Definition dMem := dMem addrSize dataBytes rfIdx dExecName.
  Definition d2w := d2w addrSize dataBytes rfIdx.

  Definition writeback := writeback addrSize dataBytes rfIdx.

  Definition inOrderEight :=
    inOrderEight iExecName dExecName
                 decodeInst execInst
                 btbIndexSize btbTagSize bhtIndexSize bhtTrainSize
                 Hbtb.

  Definition fetchBtbInl :=
    fetchBtbInl dataBytes btbIndexSize btbTagSize Hbtb f2iName.

  Definition inOrderEight1 :=
    (projT1 fetchBtbInl ++
            decRedir ++ exeRedir ++ decEpoch ++ exeEpoch ++ f2i ++
            iMem ++ i2d ++
            decode ++ bht ++ bhtTrain ++ d2r ++
            regRead ++ rf ++ bypass ++ r2e ++
            execute ++ e2m ++
            mem ++ m2d ++
            dMem ++ d2w ++
            writeback)%kami.

End Processor.


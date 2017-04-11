Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.MemTypes Ex.Fifo Ex.NativeFifo.
Require Import AbstractIsa Proc.RegFile.
Require Import Fetch IMem Decode RegRead Execute Mem DMem Writeback.

Set Implicit Arguments.

Open Scope string.

Section Processor.
  Variables addrSize dataBytes rfIdx: nat.

  Variable decodeInst: DecodeT dataBytes rfIdx.
  Variable execInst: ExecT addrSize dataBytes rfIdx.

  Definition f2iName := "f2i".
  Definition i2dName := "i2d".
  Definition d2rName := "d2r".
  Definition r2eName := "r2e".
  Definition e2mName := "e2m".
  Definition m2dName := "m2d".
  Definition d2wName := "d2w".
  Definition decName := "dec".
  Definition exeName := "exe".
  Definition bhtTrainName := "bhtTrain".

  (** TODO: need to differentiate below interfaces to memory *)
  Definition iExecName := "exec".
  Definition dExecName := "exec".

  Variables btbIndexSize btbTagSize bhtIndexSize bhtTrainSize: nat.
  Hypothesis (Hbtb: btbIndexSize + btbTagSize = addrSize).

  (** Fetch related *)
  Definition fetch := fetch addrSize dataBytes f2iName.
  Definition btb := btb btbIndexSize btbTagSize Hbtb.
  Definition decRedir := redirect addrSize decName.
  Definition exeRedir := redirect addrSize exeName.
  Definition f2i := @nativeSimpleFifo f2iName (Struct (F2I addrSize dataBytes)) Default.

  (** IMem related *)
  Definition iMem := iMem addrSize dataBytes f2iName i2dName iExecName.
  Definition i2d := @nativeSimpleFifo i2dName (Struct (I2D addrSize dataBytes)) Default.

  (** Decode related *)
  Definition decode := decode addrSize i2dName d2rName decodeInst.
  Definition bht := bht addrSize bhtIndexSize.
  Definition bhtTrain := bhtTrain addrSize bhtTrainName.
  Definition bhtTrainQ := simpleFifo bhtTrainName bhtTrainSize (Struct (bhtUpdateStr addrSize)).
  Definition d2r := @nativeSimpleFifo d2rName (Struct (D2R addrSize dataBytes rfIdx)) Default.

  (** RegRead related *)
  Definition regRead := regRead addrSize dataBytes rfIdx d2rName r2eName.
  Definition rf := regFile dataBytes rfIdx.
  Definition bypass := bypass dataBytes rfIdx.
  Definition r2e := @nativeSimpleFifo r2eName (Struct (R2E addrSize dataBytes rfIdx)) Default.

  (** Execute related *)
  Definition execute := execute r2eName e2mName bhtTrainName execInst.
  Definition e2m := @nativeSimpleFifo e2mName (Struct (E2M addrSize dataBytes rfIdx)) Default.

  (** Mem related *)
  Definition mem := mem addrSize dataBytes rfIdx e2mName m2dName.
  Definition m2d := @nativeSimpleFifo m2dName (Struct (M2D addrSize dataBytes rfIdx)) Default.

  (** DMem related *)
  Definition dMem := dMem addrSize dataBytes rfIdx m2dName d2wName dExecName.
  Definition d2w := @nativeSimpleFifo d2wName (Struct (D2W addrSize dataBytes rfIdx)) Default.

  (** Writeback related *)
  Definition writeback := writeback addrSize dataBytes rfIdx d2wName.

  Definition inOrderEight :=
    (fetch ++ btb ++ decRedir ++ exeRedir ++ decEpoch ++ exeEpoch ++ f2i ++
           iMem ++ i2d ++
           decode ++ bht ++ bhtTrain ++ bhtTrainQ ++ d2r ++
           regRead ++ rf ++ bypass ++ r2e ++
           execute ++ e2m ++
           mem ++ m2d ++
           dMem ++ d2w ++
           writeback)%kami.

End Processor.

Hint Unfold fetch btb decRedir exeRedir
     f2i iMem i2d decode bht bhtTrain d2r
     regRead rf bypass r2e execute e2m mem m2d dMem d2w
     writeback inOrderEight : ModuleDefs.
Hint Unfold f2iName i2dName d2rName r2eName e2mName
     m2dName d2wName decName exeName bhtTrainName : MethDefs.


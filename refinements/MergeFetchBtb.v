Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import Proc.AbstractIsa Proc.Fetch Proc.FetchBtb Proc.InOrderEightStage.

Set Implicit Arguments.
Open Scope string.

Section Processor.
  Variables addrSize dataBytes rfIdx: nat.

  Variable decodeInst: DecodeT dataBytes rfIdx.
  Variable execInst: ExecT addrSize dataBytes rfIdx.

  Variables btbIndexSize btbTagSize bhtIndexSize bhtTrainSize: nat.
  Hypothesis (Hbtb: btbIndexSize + btbTagSize = addrSize).

  (** Fetch related *)
  Definition decRedir := decRedir addrSize.
  Definition exeRedir := exeRedir addrSize.
  Definition f2i := f2i addrSize dataBytes.

  (** IMem related *)
  Definition iMem := iMem addrSize dataBytes.
  Definition i2d := i2d addrSize dataBytes.

  (** Decode related *)
  Definition decode := decode addrSize decodeInst.
  Definition bht := bht addrSize bhtIndexSize.
  Definition bhtTrain := bhtTrain addrSize bhtTrainSize.
  Definition d2r := d2r addrSize dataBytes rfIdx.

  Definition fetchBtb := fetchBtb dataBytes btbIndexSize btbTagSize Hbtb f2iName.

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
  Definition dMem := dMem addrSize dataBytes rfIdx.
  Definition d2w := d2w addrSize dataBytes rfIdx.

  Definition writeback := writeback addrSize dataBytes rfIdx.

  Definition inOrderEight :=
    inOrderEight decodeInst execInst
                 btbIndexSize btbTagSize bhtIndexSize bhtTrainSize
                 Hbtb.

  Definition inOrderEight0 :=
    (fetchBtb ++ decRedir ++ exeRedir ++ decEpoch ++ exeEpoch ++ f2i ++
              iMem ++ i2d ++
              decode ++ bht ++ bhtTrain ++ d2r ++
              regRead ++ rf ++ bypass ++ r2e ++
              execute ++ e2m ++
              mem ++ m2d ++
              dMem ++ d2w ++
              writeback)%kami.

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

  Hint Unfold decRedir exeRedir f2i iMem i2d
       decode bht bhtTrain d2r fetchBtb fetchBtbInl
       regRead rf bypass r2e execute e2m mem m2d dMem d2w
       writeback inOrderEight inOrderEight0 inOrderEight1 : ModuleDefs.

  Theorem inOrderEight_inOrderEight0:
    inOrderEight <<== inOrderEight0.
  Proof.
    krewrite assoc left.
    krefl.
  Qed.

  Theorem inOrderEight0_inOrderEight1:
    inOrderEight0 <<== inOrderEight1.
  Proof.
    (* TODO: below is actually [kmodularn], but need to slightly modify it. *)

    (* try (unfold MethsT; rewrite <- SemFacts.idElementwiseId). *)
    (* apply traceRefines_modular_noninteracting. *)

    (* - kequiv. *)
    (* - kequiv. *)
    (* - kequiv. *)
    (* - kequiv. *)
    (* - (* TODO: add this logic to [kdisj_regs] *) *)
    (*   unfold projT1; repeat autounfold with ModuleDefs. *)
    (*   kdisj_regs. *)
    (* - unfold projT1; repeat autounfold with ModuleDefs. *)
    (*   kdisj_regs. *)
    (* - kvr. *)
    (* - kvr. *)
    (* - unfold projT1; repeat autounfold with ModuleDefs. *)
    (*   kdisj_dms. *)
    (* - unfold projT1; repeat autounfold with ModuleDefs. *)
    (*   kdisj_cms. *)
    (* - unfold projT1; repeat autounfold with ModuleDefs. *)
    (*   kdisj_dms. *)
    (* - unfold projT1; repeat autounfold with ModuleDefs. *)
    (*   kdisj_cms. *)
    (* - knoninteracting. *)
    (* - knoninteracting. *)
    (* - apply (projT2 fetchBtbInl). *)
    (* - krefl. *)
    give_up.
  Admitted.

End Processor.


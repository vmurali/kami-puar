Require Import Kami.
Require Import Lib.CommonTactics Lib.Indexer.
Require Import Kami.Decomposition.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import Proc.AbstractIsa Proc.Fetch Proc.Decode Proc.Execute Proc.InOrderEightStage.

Set Implicit Arguments.
Open Scope string.

Section Processor.
  Variables addrSize dataBytes rfIdx: nat.

  Variable decodeInst: DecodeT dataBytes rfIdx.
  Variable execInst: ExecT addrSize dataBytes rfIdx.

  Variables btbIndexSize btbTagSize bhtIndexSize bhtTrainSize: nat.
  Hypothesis (Hbtb: btbIndexSize + btbTagSize = addrSize).

  (** Fetch related *)
  Definition fetchNondet := fetchNondet addrSize dataBytes f2iName.
  Definition decRedir := decRedir addrSize.
  Definition exeRedir := exeRedir addrSize.
  Definition f2i := f2i addrSize dataBytes.

  (** IMem related *)
  Definition iMem := iMem addrSize dataBytes.
  Definition i2d := i2d addrSize dataBytes.

  (** Decode related *)
  Definition decodeNondet := decodeNondet addrSize i2dName d2rName decodeInst.
  Definition d2r := d2r addrSize dataBytes rfIdx.

  (** RegRead related *)
  Definition regRead := regRead addrSize dataBytes rfIdx.
  Definition rf := rf dataBytes rfIdx.
  Definition bypass := bypass dataBytes rfIdx.
  Definition r2e := r2e addrSize dataBytes rfIdx.

  (** Execute related *)
  Definition executeNondet := executeNondet r2eName e2mName execInst.
  Definition e2m := e2m addrSize dataBytes rfIdx.

  (** Mem related *)
  Definition mem := mem addrSize dataBytes rfIdx.
  Definition m2d := m2d addrSize dataBytes rfIdx.

  (** DMem related *)
  Definition dMem := dMem addrSize dataBytes rfIdx.
  Definition d2w := d2w addrSize dataBytes rfIdx.

  (** Writeback related *)
  Definition writeback := writeback addrSize dataBytes rfIdx.

  (* inOrderEight :=
     (fetch ++ btb ++ decRedir ++ exeRedir ++ decEpoch ++ exeEpoch ++ f2i ++
     iMem ++ i2d ++
     decode ++ bht ++ bhtTrain ++ bhtTrainQ ++ d2r ++
     regRead ++ rf ++ bypass ++ r2e ++
     execute ++ e2m ++
     mem ++ m2d ++
     dMem ++ d2w ++
     writeback)%kami.
   *)
  Definition inOrderEight :=
    inOrderEight decodeInst execInst
                 btbIndexSize btbTagSize bhtIndexSize bhtTrainSize
                 Hbtb.

  Definition inOrderEight0 :=
    (fetchNondet ++ decRedir ++ exeRedir ++ decEpoch ++ exeEpoch ++ f2i ++
                 iMem ++ i2d ++
                 decodeNondet ++ d2r ++
                 regRead ++ rf ++ bypass ++ r2e ++
                 executeNondet ++ e2m ++
                 mem ++ m2d ++
                 dMem ++ d2w ++
                 writeback)%kami.

  Section Refinement.

    (* Eval compute in (Struct.namesOf (getRegInits inOrderEight)). *)
    (* Eval compute in (Struct.namesOf (getRegInits inOrderEight0)). *)

    Local Definition dropRegs : list string :=
      ["full.bhtTrain"; "empty.bhtTrain"; "deqP.bhtTrain"; "enqP.bhtTrain"; "elt.bhtTrain";
         "satCnt"; "btbValid"; "btbTags"; "btbTargets"].

    Local Definition theta (s: RegsT) : RegsT := M.complement s dropRegs.

    (* Eval compute in (getDefs inOrderEight). *)
    (* Eval compute in (getDefs inOrderEight0). *)

    Local Definition dropMeths : list string :=
      ["firstElt.bhtTrain"; "deq.bhtTrain"; "enq.bhtTrain"; "update"; "predTaken";
         "btbUpdate"; "btbPredPc"].
    (* pose (getDefs inOrderEight) as pdefs; compute in pdefs. *)
    (* pose (getDefs inOrderEight0) as ndefs; compute in ndefs. *)
    (* pose (fold_left (fun nl e => *)
    (*                    if in_dec string_dec e ndefs then nl else e :: nl) pdefs nil) as ddefs. *)
    (* compute in ddefs. *)

    Local Definition p (n: string) (v: (sigT SignT)): option (sigT SignT) :=
      if in_dec string_dec n dropMeths
      then None
      else Some v.

    Local Definition ruleMap (o: RegsT) (n: string) : option string := Some n.
    
    Theorem inOrderEight_inOrderEight0: inOrderEight <<== inOrderEight0.
    Proof.
      (* apply traceRefines_labelMap_weakening with (vp:= p); [kequiv| |]. *)
      (* apply decompositionDrop with (theta:= theta) (ruleMap:= ruleMap). *)
    Admitted.

  End Refinement.
  
End Processor.


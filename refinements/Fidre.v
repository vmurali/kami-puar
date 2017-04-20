Require Import Kami.
Require Import Lib.CommonTactics Lib.Indexer Lib.VectorFacts.
Require Import Kami.Decomposition Kami.ModuleBoundEx.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import Proc.AbstractIsa Proc.Fetch Proc.Decode Proc.RegRead Proc.Execute
        Proc.InOrderEightStage.
Require Import DropBranchPredictors.

Set Implicit Arguments.
Open Scope string.

Section Processor.
  Variables addrSize dataBytes rfIdx: nat.

  Variable decodeInst: DecodeT dataBytes rfIdx.
  Variable execInst: ExecT addrSize dataBytes rfIdx.

  (** Fetch related *)
  Definition fetchNondet := fetchNondet addrSize dataBytes.
  Definition decRedir := decRedir addrSize.
  Definition exeRedir := exeRedir addrSize.
  Definition f2i := f2i addrSize dataBytes.

  (** IMem related *)
  Definition iMem := iMem addrSize dataBytes.
  Definition i2d := i2d addrSize dataBytes.

  (** Decode related *)
  Definition decodeNondet := decodeNondet addrSize decodeInst.
  Definition d2r := d2r addrSize dataBytes rfIdx.

  (** RegRead related *)
  Definition regRead := regRead addrSize dataBytes rfIdx.
  Definition r2e := r2e addrSize dataBytes rfIdx.

  (** Execute related *)
  Definition executeNondet := executeNondet execInst.

  Definition fidreComb :=
    (fetchNondet ++ decRedir ++ exeRedir ++ exeEpoch ++ f2i
                 ++ iMem ++ i2d
                 ++ decodeNondet ++ d2r
                 ++ regRead ++ r2e
                 ++ executeNondet)%kami.

  Hint Unfold fetchNondet decRedir exeRedir f2i
       iMem i2d decodeNondet d2r regRead r2e executeNondet
       fidreComb: ModuleDefs. (* for kinline_compute *)

  Lemma fidreComb_ModEquiv: ModPhoasWf fidreComb.
  Proof. kequiv. Qed.

  (* Definition fidreInl: Modules * bool. *)
  (* Proof. *)
  (*   remember (inlineF fidreComb) as inlined. *)
  (*   kinline_compute_in Heqinlined. *)
  (*   match goal with *)
  (*   | [H: inlined = ?m |- _] => *)
  (*     exact m *)
  (*   end. *)
  (* Defined. *)

  (* Definition fidreInl : sigT (fun m: Modules => fidreComb <<== m). *)
  (* Proof. *)
  (*   pose proof (inlineF_refines *)
  (*                 (fidreComb_ModEquiv type typeUT) *)
  (*                 (Reflection.noDupStr_NoDup (Struct.namesOf (getDefsBodies fidreComb)) eq_refl)) *)
  (*     as Him. *)
  (*   unfold MethsT in Him; rewrite <-SemFacts.idElementwiseId in Him. *)
  (*   match goal with *)
  (*   | [H: context[inlineF ?m] |- _] => set m as origm in H at 2 *)
  (*   end. *)
  (*   kinline_compute_in Him. *)
  (*   unfold origm in *. *)
  (*   specialize (Him eq_refl). *)
  (*   exact (existT _ _ Him). *)
  (* Defined. *)

End Processor.


Require Import Kami.
Require Import Lib.CommonTactics Lib.Indexer Lib.VectorFacts.
Require Import Kami.Decomposition Kami.ModuleBoundEx.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import Proc.AbstractIsa Proc.Fetch Proc.Decode Proc.RegRead Proc.Execute
        Proc.InOrderEightStage.
Require Import DropBranchPredictors Fidre.

Set Implicit Arguments.
Open Scope string.

Section Processor.
  Variables addrSize dataBytes rfIdx: nat.

  Variable decodeInst: DecodeT dataBytes rfIdx.
  Variable execInst: ExecT addrSize dataBytes rfIdx.

  (** Fetch related *)
  Definition fetchNondet := fetchNondet addrSize dataBytes.
  Definition fetchNondetNR := fetchNondetNR addrSize dataBytes f2iName.
  Definition decRedir := decRedir addrSize.
  Definition exeRedir := exeRedir addrSize.
  Definition f2i := f2i addrSize dataBytes.

  (** IMem related *)
  Definition iMem := iMem addrSize dataBytes.
  Definition i2d := i2d addrSize dataBytes.

  (** Decode related *)
  Definition decodeNondet := decodeNondet addrSize decodeInst.
  Definition decodeNondetNR := decodeNondetNR addrSize i2dName d2rName decodeInst.
  Definition d2r := d2r addrSize dataBytes rfIdx.

  (** RegRead related *)
  Definition regRead := regRead addrSize dataBytes rfIdx.
  Definition rf := rf dataBytes rfIdx.
  Definition bypass := bypass dataBytes rfIdx.
  Definition r2e := r2e addrSize dataBytes rfIdx.

  (** Execute related *)
  Definition executeNondet := executeNondet execInst.
  Definition executeNondetNR := executeNondetNR r2eName e2mName execInst.
  Definition e2m := e2m addrSize dataBytes rfIdx.

  (** Mem related *)
  Definition mem := mem addrSize dataBytes rfIdx.
  Definition m2d := m2d addrSize dataBytes rfIdx.

  (** DMem related *)
  Definition dMem := dMem addrSize dataBytes rfIdx.
  Definition d2w := d2w addrSize dataBytes rfIdx.

  (** Writeback related *)
  Definition writeback := writeback addrSize dataBytes rfIdx.

  Definition fidreComb := fidreComb decodeInst execInst.
  
  Definition fidreNR :=
    (fetchNondetNR ++ f2i
                   ++ iMem ++ i2d
                   ++ decodeNondetNR ++ d2r
                   ++ regRead ++ r2e
                   ++ executeNondetNR)%kami.

  Section RefinementNR.

    Definition F2I := F2I addrSize dataBytes.
    Definition I2D := I2D addrSize dataBytes.
    Definition D2R := D2R addrSize dataBytes rfIdx.
    Definition R2E := R2E addrSize dataBytes rfIdx.

    Fixpoint getArchPcF2I (decEpoch exeEpoch: bool) (f2i: list (type (Struct F2I)))
      : option (fullType type (SyntaxKind (Bit addrSize))) :=
      match f2i with
      | nil => None
      | e :: f2i' =>
        if (eqb (e Fin.F1 (Fin.FS (Fin.FS Fin.F1))) decEpoch &&
                eqb (e Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) exeEpoch)
        then Some (e Fin.F1 Fin.F1)
        else getArchPcF2I decEpoch exeEpoch f2i'
      end.

    Fixpoint getArchPcI2D (decEpoch exeEpoch: bool) (i2d: list (type (Struct I2D)))
      : option (fullType type (SyntaxKind (Bit addrSize))) :=
      match i2d with
      | nil => None
      | e :: i2d' =>
        if (eqb (e Fin.F1 (Fin.FS (Fin.FS Fin.F1))) decEpoch &&
                eqb (e Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) exeEpoch)
        then Some (e Fin.F1 Fin.F1)
        else getArchPcI2D decEpoch exeEpoch i2d'
      end.

    Fixpoint getArchPcD2R (exeEpoch: bool) (d2r: list (type (Struct D2R)))
      : option (fullType type (SyntaxKind (Bit addrSize))) :=
      match d2r with
      | nil => None
      | e :: d2r' =>
        if (eqb (e (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) exeEpoch)
        then Some (e Fin.F1)
        else getArchPcD2R exeEpoch d2r'
      end.

    Fixpoint getArchPcR2E (exeEpoch: bool) (r2e: list (type (Struct R2E)))
      : option (fullType type (SyntaxKind (Bit addrSize))) :=
      match r2e with
      | nil => None
      | e :: r2e' =>
        if (eqb (e (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))) exeEpoch)
        then Some (e Fin.F1)
        else getArchPcR2E exeEpoch r2e'
      end.

    Local Definition otake {A} (oa: option A) (default: A): A :=
      match oa with
      | Some a => a
      | None => default
      end.
    Infix ">>=" := otake (at level 0, right associativity).

    Definition getArchPc (pcv: fullType type (SyntaxKind (Bit addrSize)))
               (decEpoch exeEpoch: fullType type (SyntaxKind Bool))
               (f2i: fullType type (@NativeKind (list (type (Struct F2I))) nil))
               (i2d: fullType type (@NativeKind (list (type (Struct I2D))) nil))
               (d2r: fullType type (@NativeKind (list (type (Struct D2R))) nil))
               (r2e: fullType type (@NativeKind (list (type (Struct R2E))) nil)) :=
      (getArchPcR2E exeEpoch r2e)
        >>= (getArchPcD2R exeEpoch d2r)
        >>= (getArchPcI2D decEpoch exeEpoch i2d)
        >>= (getArchPcF2I decEpoch exeEpoch f2i)
        >>= pcv.

    Definition f2iFilter (decEpoch exeEpoch: bool)
               (f2i: list (type (Struct F2I)))
      : fullType type (@NativeKind (list (type (Struct F2I))) nil) :=
      filter
        (fun e : type (Struct F2I) =>
           eqb (e Fin.F1 (Fin.FS (Fin.FS Fin.F1))) decEpoch &&
               eqb (e Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) exeEpoch) f2i.

    Definition i2dFilter (decEpoch exeEpoch: bool)
               (i2d: list (type (Struct I2D)))
      : fullType type (@NativeKind (list (type (Struct I2D))) nil) :=
      filter
        (fun e : type (Struct I2D) =>
           eqb (e Fin.F1 (Fin.FS (Fin.FS Fin.F1))) decEpoch &&
               eqb (e Fin.F1 (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) exeEpoch) i2d.

    Definition d2rFilter (exeEpoch: bool)
               (d2r: list (type (Struct D2R)))
      : fullType type (@NativeKind (list (type (Struct D2R))) nil) :=
      filter
        (fun e : type (Struct D2R) =>
           eqb (e (Fin.FS (Fin.FS (Fin.FS Fin.F1)))) exeEpoch) d2r.

    Definition r2eFilter (exeEpoch: bool)
               (r2e: list (type (Struct R2E)))
      : fullType type (@NativeKind (list (type (Struct R2E))) nil) :=
      filter
        (fun e : type (Struct R2E) =>
           eqb (e (Fin.FS (Fin.FS (Fin.FS (Fin.FS (Fin.FS Fin.F1)))))) exeEpoch) r2e.

    Local Definition thetaR (ir sr: RegsT): Prop.
    Proof.
      kexistnv "pc" pcv ir (SyntaxKind (Bit addrSize)).
      kexistnv "decEpoch" decEpochv ir (SyntaxKind Bool).
      kexistnv "exeEpoch" exeEpochv ir (SyntaxKind Bool).
      kexistnv "f2i" -- "elt" f2iv ir (@NativeKind (list (type (Struct F2I))) nil).
      kexistnv "i2d" -- "elt" i2dv ir (@NativeKind (list (type (Struct I2D))) nil).
      kexistnv "d2r" -- "elt" d2rv ir (@NativeKind (list (type (Struct D2R))) nil).
      kexistnv "r2e" -- "elt" r2ev ir (@NativeKind (list (type (Struct R2E))) nil).

      exact (sr =
             ["pc" <- existT _ _ pcv]
             +["f2i" -- "elt" <- existT _ _ (f2iFilter decEpochv exeEpochv f2iv)]
             +["i2d" -- "elt" <- existT _ _ (i2dFilter decEpochv exeEpochv i2dv)]
             +["d2r" -- "elt" <- existT _ _ (d2rFilter exeEpochv d2rv)]
             +["r2e" -- "elt" <- existT _ _ (r2eFilter exeEpochv r2ev)]
             +["archPc" <- existT _ _ (getArchPc pcv decEpochv exeEpochv
                                                 f2iv i2dv d2rv r2ev)])%fmap.
    Defined.

    Hint Unfold F2I I2D D2R R2E : MethDefs.
    Hint Unfold getArchPcF2I getArchPcI2D getArchPcD2R getArchPcR2E otake getArchPc
         f2iFilter i2dFilter d2rFilter r2eFilter thetaR : MapDefs.

    (* TODO *)
    Local Definition ruleMap (o: RegsT) (n: string) := Some n.
    Hint Unfold ruleMap : MethDefs.

    Theorem fidreComb_fidreNR: fidreComb <<== fidreNR.
    Proof.
      (* apply stepRefinementR with (ruleMap:= ruleMap) (thetaR:= thetaR). *)

      (* - kdecompose_regrel_init. *)
      (*   meqReify. *)

      (* - intros. *)
    Admitted.

  End RefinementNR.
  
End Processor.


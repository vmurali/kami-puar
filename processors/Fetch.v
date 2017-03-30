Require Import Kami.
Require Import Lib.Indexer.
Require Import Ex.MemTypes Ex.OneEltFifo.

(* NOTE: Let's add the exception mechanism after proving without it. *)
(* Require Import Exception. *)

Set Implicit Arguments.
Open Scope string.

Section Processor.
  Variables addrSize dataBytes rfIdx: nat.

  Section BTB.
    Variable indexSize tagSize: nat.
    Hypothesis (Haddr: indexSize + tagSize = addrSize).

    Definition getIndex {ty} (pcv: fullType ty (SyntaxKind (Bit addrSize))):
      Expr ty (SyntaxKind (Bit indexSize)) :=
      UniBit (Trunc _ _)
             (eq_rect_r (fun n => Expr ty (SyntaxKind (Bit n)))
                        (#pcv >> $$(natToWord 2 2))%kami_expr
                        Haddr).

    Definition getTag {ty} (pcv: fullType ty (SyntaxKind (Bit addrSize))):
      Expr ty (SyntaxKind (Bit tagSize)) :=
      UniBit (TruncLsb _ _)
             (eq_rect_r (fun n => Expr ty (SyntaxKind (Bit n)))
                        (#pcv)%kami_expr
                        Haddr).

    Definition BtbUpdateStr :=
      STRUCT { "curPc" :: Bit addrSize; "nextPc" :: Bit addrSize }.

    Definition btbPredPc := MethodSig "predPc"(Bit addrSize): Bit addrSize.
    Definition btbUpdate := MethodSig "update"(Struct BtbUpdateStr): Void.

    Definition btb :=
      MODULE {
          Register "targets" : Vector (Bit addrSize) indexSize <- Default
          with Register "tags" : Vector (Bit tagSize) indexSize <- Default
          with Register "valid" : Vector Bool indexSize <- Default

          with Method "predPc" (pc: Bit addrSize): Bit addrSize :=
            LET index <- getIndex pc;
            LET tag <- getTag pc;

            Read targets <- "targets";
            Read valid <- "valid";
            Read tags <- "tags";

            If (#valid@[#index] && (#tag == #tags@[#index]))
            then Ret #targets@[#index]
            else Ret (#pc + $4)
            as npc;
            
            Ret #npc
                
          with Method "update" (upd: Struct BtbUpdateStr): Void :=
            LET curPc <- #upd ! BtbUpdateStr @."curPc";
            LET nextPc <- #upd ! BtbUpdateStr @."nextPc";
            LET index <- getIndex curPc;
            LET tag <- getTag curPc;

            Read targets: Vector (Bit addrSize) indexSize <- "targets";
            Read valid: Vector Bool indexSize <- "valid";
            Read tags: Vector (Bit tagSize) indexSize <- "tags";

            If (#nextPc != (#curPc + $4))
            then
              Write "valid" <- #valid@[#index <- $$true];
              Write "tags" <- #tags@[#index <- #tag];
              Write "targets" <- #targets@[#index <- #nextPc];
              Retv
            else
              If (#tag == #tags@[#index])
              then Write "valid" <- #valid@[#index <- $$false]; Retv;
              Retv;
            Retv
      }.

  End BTB.

  Section Redirect.
    Variable redirName: string.

    Definition redirectStr :=
      STRUCT { "pc" :: Bit addrSize; "nextPc" :: Bit addrSize }.
    Definition RedirectK := Struct (Maybe (Struct redirectStr)).

    Definition redirGet := MethodSig (redirName -- "get")(): RedirectK.
    Definition redirSetInvalid := MethodSig (redirName -- "setInvalid")(): Void.
    Definition redirSetValid := MethodSig (redirName -- "setValid")(Struct redirectStr): Void.

    Definition redirect :=
      MODULE {
          Register redirName : RedirectK <- Default

          with Method (redirName -- "get") (): RedirectK :=
            Read redir <- redirName;
            Ret #redir

          with Method (redirName -- "setInvalid") (): Void :=
            Write redirName: RedirectK <- STRUCT { "isValid" ::= $$false;
                                                   "value" ::= $$Default };
            Retv

          with Method (redirName -- "setValid")(v: Struct redirectStr): Void :=
            Write redirName: RedirectK <- STRUCT { "isValid" ::= $$true;
                                                   "value" ::= #v };
            Retv
        }.

  End Redirect.

  Section Epoch.
    Variable epochName: string.

    Definition getEpoch := MethodSig (epochName -- "getEpoch")() : Bool.
    Definition toggleEpoch := MethodSig (epochName -- "toggleEpoch")() : Void.

    Definition epoch :=
      MODULE {
        Register epochName : Bool <- false

        with Method (epochName -- "getEpoch") () : Bool :=
          Read epoch <- epochName;
          Ret #epoch

        with Method (epochName -- "toggleEpoch") () : Void :=
          Read epoch <- epochName;
          Write epochName <- !#epoch;
          Retv
      }.

  End Epoch.

  Section Fetch.
    Variable (f2iName: string).

    Definition F2D :=
      STRUCT { "pc" :: Bit addrSize;
               "predPc" :: Bit addrSize;
               "decEpoch" :: Bool;
               "exeEpoch" :: Bool }.

    Definition F2I :=
      STRUCT { "f2dOrig" :: Struct F2D;
               "iMemReq" :: Struct (RqFromProc dataBytes (Bit addrSize)) }.

    Definition f2iEnq := MethodSig (f2iName -- "enq")(Struct F2I): Void.

    Definition fetch :=
      MODULE {
        Register "pc" : Bit addrSize <- Default

        with Rule "doFetch" :=
          Read pc <- "pc";
          Call predPc <- btbPredPc(#pc);
          Write "pc" <- #predPc;
          Call decEpoch <- (getEpoch "dec")();
          Call exeEpoch <- (getEpoch "exe")();
          Call f2iEnq (
                 STRUCT { "f2dOrig" ::= STRUCT { "pc" ::= #pc;
                                                 "predPc" ::= #predPc;
                                                 "decEpoch" ::= #decEpoch;
                                                 "exeEpoch" ::= #exeEpoch };
                          "iMemReq" ::= STRUCT { "addr" ::= #pc;
                                                 "op" ::= $$false;
                                                 "data" ::= $$Default }
                        });
          Retv

        with Rule "redirect" :=
          Call exeRedir <- (redirGet "exe")();
          If (#exeRedir!(Maybe (Struct redirectStr))@."isValid")
          then
            LET r <- #exeRedir!(Maybe (Struct redirectStr))@."value";
            Write "pc" <- #r!redirectStr@."nextPc";
            Call btbUpdate(STRUCT { "curPc" ::= #r!redirectStr@."pc";
                                    "nextPc" ::= #r!redirectStr@."nextPc" });
            Call (toggleEpoch "exe")();
            Retv
          else
            Call decRedir <- (redirGet "dec")();
            If (#decRedir!(Maybe (Struct redirectStr))@."isValid")
            then
              LET r <- #decRedir!(Maybe (Struct redirectStr))@."value";
              Write "pc" <- #r!redirectStr@."nextPc";
              Call btbUpdate(STRUCT { "curPc" ::= #r!redirectStr@."pc";
                                      "nextPc" ::= #r!redirectStr@."nextPc" });
              Call (toggleEpoch "dec")();
              Retv;
            Retv;
          Call (redirSetInvalid "exe")();
          Call (redirSetInvalid "dec")();
          Retv
      }.

  End Fetch.

End Processor.

Hint Unfold btb redirect epoch fetch : ModuleDefs.
Hint Unfold getIndex getTag BtbUpdateStr btbPredPc btbUpdate
     redirectStr RedirectK redirGet redirSetInvalid redirSetValid
     getEpoch toggleEpoch
     F2D F2I f2iEnq : MethDefs.

Section Wf.
  Variables addrSize dataBytes rfIdx: nat.
  Variable indexSize tagSize: nat.
  Hypothesis (Haddr: indexSize + tagSize = addrSize).

  Lemma btb_ModEquiv:
    ModPhoasWf (btb indexSize tagSize Haddr).
  Proof. kequiv. Qed.

  Lemma redirect_ModEquiv:
    forall redirName, ModPhoasWf (redirect addrSize redirName).
  Proof. kequiv. Qed.

  Lemma epoch_ModEquiv:
    forall epochName, ModPhoasWf (epoch epochName).
  Proof. kequiv. Qed.

  Lemma fetch_ModEquiv:
    forall f2iName, ModPhoasWf (fetch addrSize dataBytes f2iName).
  Proof. kequiv. Qed.

End Wf.

Hint Resolve btb_ModEquiv redirect_ModEquiv epoch_ModEquiv fetch_ModEquiv.


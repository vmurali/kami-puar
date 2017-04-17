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
    Variables indexSize tagSize: nat. (* should satisfy [indexSize + tagSize = addrSize] *)
    Variables (getIndex: forall {ty}, fullType ty (SyntaxKind (Bit addrSize)) ->
                                      Expr ty (SyntaxKind (Bit indexSize)))
              (getTag: forall {ty}, fullType ty (SyntaxKind (Bit addrSize)) ->
                                    Expr ty (SyntaxKind (Bit tagSize))).

    Definition BtbUpdateStr :=
      STRUCT { "curPc" :: Bit addrSize; "nextPc" :: Bit addrSize }.

    Definition btbPredPc := MethodSig "btbPredPc"(Bit addrSize): Bit addrSize.
    Definition btbUpdate := MethodSig "btbUpdate"(Struct BtbUpdateStr): Void.

    Definition btb :=
      MODULE {
          Register "btbTargets" : Vector (Bit addrSize) indexSize <- Default
          with Register "btbTags" : Vector (Bit tagSize) indexSize <- Default
          with Register "btbValid" : Vector Bool indexSize <- Default

          with Method "btbPredPc" (pc: Bit addrSize): Bit addrSize :=
            LET index <- getIndex _ pc;
            LET tag <- getTag _ pc;

            Read targets <- "btbTargets";
            Read valid <- "btbValid";
            Read tags <- "btbTags";

            If (#valid@[#index] && (#tag == #tags@[#index]))
            then Ret #targets@[#index]
            else Ret (#pc + $4)
            as npc;
            
            Ret #npc
                
          with Method "btbUpdate" (upd: Struct BtbUpdateStr): Void :=
            LET curPc <- #upd ! BtbUpdateStr @."curPc";
            LET nextPc <- #upd ! BtbUpdateStr @."nextPc";
            LET index <- getIndex _ curPc;
            LET tag <- getTag _ curPc;

            Read targets: Vector (Bit addrSize) indexSize <- "btbTargets";
            Read valid: Vector Bool indexSize <- "btbValid";
            Read tags: Vector (Bit tagSize) indexSize <- "btbTags";

            If (#nextPc != (#curPc + $4))
            then
              Write "btbValid" <- #valid@[#index <- $$true];
              Write "btbTags" <- #tags@[#index <- #tag];
              Write "btbTargets" <- #targets@[#index <- #nextPc];
              Retv
            else
              If (#tag == #tags@[#index])
              then Write "btbValid" <- #valid@[#index <- $$false]; Retv;
              Retv;
            Retv
      }.

  End BTB.

  Section Redirect.
    Variable redirName: string.

    Definition redirectStr :=
      STRUCT { "pc" :: Bit addrSize; "nextPc" :: Bit addrSize }.
    Definition RedirectK := Struct (Maybe (Struct redirectStr)).

    Definition redirGet := MethodSig (redirName -- "redirGet")(): RedirectK.
    Definition redirSetInvalid := MethodSig (redirName -- "redirSetInvalid")(): Void.
    Definition redirSetValid := MethodSig (redirName -- "redirSetValid")(Struct redirectStr): Void.

    Definition redirect :=
      MODULE {
          Register redirName : RedirectK <- Default

          with Method (redirName -- "redirGet") (): RedirectK :=
            Read redir <- redirName;
            Ret #redir

          with Method (redirName -- "redirSetInvalid") (): Void :=
            Write redirName: RedirectK <- STRUCT { "isValid" ::= $$false;
                                                   "value" ::= $$Default };
            Retv

          with Method (redirName -- "redirSetValid")(v: Struct redirectStr): Void :=
            Write redirName: RedirectK <- STRUCT { "isValid" ::= $$true;
                                                   "value" ::= #v };
            Retv
        }.

  End Redirect.

  Section DecEpoch.
    Definition decGetEpoch1 := MethodSig "decGetEpoch1"() : Bool.
    Definition decGetEpoch2 := MethodSig "decGetEpoch2"() : Bool.
    Definition decToggleEpoch := MethodSig "decToggleEpoch"() : Void.

    Definition decEpoch :=
      MODULE {
        Register "decEpoch" : Bool <- false

        with Method "decGetEpoch1" () : Bool :=
          Read epoch <- "decEpoch";
          Ret #epoch

        with Method "decGetEpoch2" () : Bool :=
          Read epoch <- "decEpoch";
          Ret #epoch

        with Method "decToggleEpoch" () : Void :=
          Read epoch <- "decEpoch";
          Write "decEpoch" <- !#epoch;
          Retv
      }.

  End DecEpoch.

  Section ExeEpoch.
    Definition exeGetEpoch1 := MethodSig "exeGetEpoch1"() : Bool.
    Definition exeGetEpoch2 := MethodSig "exeGetEpoch2"() : Bool.
    Definition exeGetEpoch3 := MethodSig "exeGetEpoch3"() : Bool.
    Definition exeToggleEpoch := MethodSig "exeToggleEpoch"() : Void.

    Definition exeEpoch :=
      MODULE {
        Register "exeEpoch" : Bool <- false

        with Method "exeGetEpoch1" () : Bool :=
          Read epoch <- "exeEpoch";
          Ret #epoch

        with Method "exeGetEpoch2" () : Bool :=
          Read epoch <- "exeEpoch";
          Ret #epoch

        with Method "exeGetEpoch3" () : Bool :=
          Read epoch <- "exeEpoch";
          Ret #epoch

        with Method "exeToggleEpoch" () : Void :=
          Read epoch <- "exeEpoch";
          Write "exeEpoch" <- !#epoch;
          Retv
      }.

  End ExeEpoch.

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
          Call decEpoch <- decGetEpoch1();
          Call exeEpoch <- exeGetEpoch1();
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

        with Rule "redirectExe" :=
          Call exeRedir <- (redirGet "exe")();
          Assert (#exeRedir!(Maybe (Struct redirectStr))@."isValid");
          LET r <- #exeRedir!(Maybe (Struct redirectStr))@."value";
          Write "pc" <- #r!redirectStr@."nextPc";
          Call btbUpdate(STRUCT { "curPc" ::= #r!redirectStr@."pc";
                                  "nextPc" ::= #r!redirectStr@."nextPc" });
          Call exeToggleEpoch();
          Call (redirSetInvalid "exe")();
          Call (redirSetInvalid "dec")();
          Retv

        with Rule "redirectDec" :=
          Call exeRedir <- (redirGet "exe")();
          Assert !(#exeRedir!(Maybe (Struct redirectStr))@."isValid");
          Call decRedir <- (redirGet "dec")();
          Assert (#decRedir!(Maybe (Struct redirectStr))@."isValid");
          LET r <- #decRedir!(Maybe (Struct redirectStr))@."value";
          Write "pc" <- #r!redirectStr@."nextPc";
          Call btbUpdate(STRUCT { "curPc" ::= #r!redirectStr@."pc";
                                  "nextPc" ::= #r!redirectStr@."nextPc" });
          Call decToggleEpoch();
          Call (redirSetInvalid "dec")();
          Retv
      }.

    Definition fetchNondet :=
      MODULE {
        Register "pc" : Bit addrSize <- Default

        with Rule "doFetch" :=
          Read pc <- "pc";
          Nondet predPc : SyntaxKind (Bit addrSize);
          Write "pc" <- #predPc;
          Call decEpoch <- decGetEpoch1();
          Call exeEpoch <- exeGetEpoch1();
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

        with Rule "redirectExe" :=
          Call exeRedir <- (redirGet "exe")();
          Assert (#exeRedir!(Maybe (Struct redirectStr))@."isValid");
          LET r <- #exeRedir!(Maybe (Struct redirectStr))@."value";
          Write "pc" <- #r!redirectStr@."nextPc";
          Call exeToggleEpoch();
          Call (redirSetInvalid "exe")();
          Call (redirSetInvalid "dec")();
          Retv

        with Rule "redirectDec" :=
          Call exeRedir <- (redirGet "exe")();
          Assert !(#exeRedir!(Maybe (Struct redirectStr))@."isValid");
          Call decRedir <- (redirGet "dec")();
          Assert (#decRedir!(Maybe (Struct redirectStr))@."isValid");
          LET r <- #decRedir!(Maybe (Struct redirectStr))@."value";
          Write "pc" <- #r!redirectStr@."nextPc";
          Call decToggleEpoch();
          Call (redirSetInvalid "dec")();
          Retv
      }.
    
  End Fetch.

End Processor.

Hint Unfold btb redirect decEpoch exeEpoch fetch fetchNondet : ModuleDefs.
Hint Unfold BtbUpdateStr btbPredPc btbUpdate
     redirectStr RedirectK redirGet redirSetInvalid redirSetValid
     decGetEpoch1 decGetEpoch2 decToggleEpoch
     exeGetEpoch1 exeGetEpoch2 exeGetEpoch3 exeToggleEpoch
     F2D F2I f2iEnq : MethDefs.

Section Wf.
  Variables addrSize dataBytes rfIdx: nat.
  Variable indexSize tagSize: nat.
  Variables (getIndex: forall {ty}, fullType ty (SyntaxKind (Bit addrSize)) ->
                                    Expr ty (SyntaxKind (Bit indexSize)))
            (getTag: forall {ty}, fullType ty (SyntaxKind (Bit addrSize)) ->
                                  Expr ty (SyntaxKind (Bit tagSize))).

  Lemma btb_ModEquiv:
    ModPhoasWf (btb getIndex getTag).
  Proof. kequiv. Qed.

  Lemma redirect_ModEquiv:
    forall redirName, ModPhoasWf (redirect addrSize redirName).
  Proof. kequiv. Qed.

  Lemma decEpoch_ModEquiv:
    ModPhoasWf decEpoch.
  Proof. kequiv. Qed.

  Lemma exeEpoch_ModEquiv:
    ModPhoasWf exeEpoch.
  Proof. kequiv. Qed.

  Lemma fetch_ModEquiv:
    forall f2iName, ModPhoasWf (fetch addrSize dataBytes f2iName).
  Proof. kequiv. Qed.

  Lemma fetchNondet_ModEquiv:
    forall f2iName, ModPhoasWf (fetchNondet addrSize dataBytes f2iName).
  Proof. kequiv. Qed.

  Lemma btb_ModRegsWf:
    ModRegsWf (btb getIndex getTag).
  Proof. kvr. Qed.

  Lemma redirect_ModRegsWf:
    forall redirName, ModRegsWf (redirect addrSize redirName).
  Proof. kvr. Qed.

  Lemma decEpoch_ModRegsWf:
    ModRegsWf decEpoch.
  Proof. kvr. Qed.

  Lemma exeEpoch_ModRegsWf:
    ModRegsWf exeEpoch.
  Proof. kvr. Qed.

  Lemma fetch_ModRegsWf:
    forall f2iName, ModRegsWf (fetch addrSize dataBytes f2iName).
  Proof. kvr. Qed.

  Lemma fetchNondet_ModRegsWf:
    forall f2iName, ModRegsWf (fetchNondet addrSize dataBytes f2iName).
  Proof. kvr. Qed.

End Wf.

Hint Resolve btb_ModEquiv redirect_ModEquiv decEpoch_ModEquiv exeEpoch_ModEquiv
     fetch_ModEquiv fetchNondet_ModEquiv.
Hint Resolve btb_ModRegsWf redirect_ModRegsWf decEpoch_ModRegsWf exeEpoch_ModRegsWf
     fetch_ModRegsWf fetchNondet_ModRegsWf.


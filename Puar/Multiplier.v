Require Import Kami.
Require Import Lib.Indexer Lib.Struct Lib.FMap Lib.Reflection.
Require Import Kami.Tactics Kami.SemFacts Kami.StepDet.
Require Import Puar.Useful FunctionalExtensionality.

Set Implicit Arguments.
Open Scope string.

(* Below implements a radix-4 Booth Multiplier.
 *
 * Note that the Booth multiplication algorithm is naturally designed
 * for signed integers, so we need to add sign bits (0) for unsigned integers
 * and their multiplication. It means we have to deal with 65 bits for 64-bit
 * unsigned multiplication.
 *
 * Here we assume the multiplier always takes _65-bit signed integers_ as
 * arguments.
 *)
Section Multiplier64.
  (* NOTE: it's hard to declare [LogNumPhases] and [NumBitsPerPhase] as 
   * variables, since truncation and extension require certain equation 
   * w.r.t. bit-lengths.
   *)
  (* Variable MultLogNumPhases MultNumStepsPerPhase: nat. *)
  Definition MultLogNumPhases := 3.
  Definition MultNumStepsPerPhase := 4.
  (* 2*4 = 8 bits are calculated per a phase. *)
  Definition MultNumBitsPerPhase := 2 * MultNumStepsPerPhase. 

  Definition MultNumPhases := wordToNat (wones MultLogNumPhases) + 1. (* 2^3 = 8 *)
  Definition MultNumBits := MultNumPhases * MultNumBitsPerPhase. (* 8*8 = 64 *)
  Definition MultNumBitsExt := MultNumBits + 1. (* 8*8 + 1 = 65 *)
  Definition MultBits := 2 * MultNumBitsExt + 2.

  Definition MultInStr := STRUCT { "multiplicand" :: Bit MultNumBitsExt;
                                   "multiplier" :: Bit MultNumBitsExt }.
  Definition MultOutStr := STRUCT { "high" :: Bit MultNumBits;
                                    "low" :: Bit MultNumBits }.

  Definition multRegister := MethodSig "multRegister"(Struct MultInStr): Void.
  Definition multGetResult := MethodSig "multGetResult"(Void): Struct MultOutStr.

  Definition boothStep' {ty}
             (m_pos m_neg: fullType ty (SyntaxKind (Bit MultBits)))
             (p: Expr ty (SyntaxKind (Bit MultBits)))
             (pr: Expr ty (SyntaxKind (Bit 2))) :=
    (IF (pr == $$(WO~0~1)) then p + #m_pos
     else IF (pr == $$(WO~1~0)) then p - #m_pos
     else p)%kami_expr.

  Definition boothStep {ty}
             (m_pos m_neg: fullType ty (SyntaxKind (Bit MultBits)))
             (p: Expr ty (SyntaxKind (Bit ((MultBits - 2) + 2))))
    : Expr ty (SyntaxKind (Bit MultBits)) :=
    (boothStep' m_pos m_neg p (UniBit (Trunc 2 _) p) >> $$(WO~1))%kami_expr.

  Definition booth4Step' {ty}
             (m_pos m_neg: fullType ty (SyntaxKind (Bit MultBits)))
             (p: Expr ty (SyntaxKind (Bit MultBits)))
             (pr: Expr ty (SyntaxKind (Bit 3))) :=
    (IF (pr == $$(WO~0~0~1)) then p + #m_pos
     else IF (pr == $$(WO~0~1~0)) then p + #m_pos
     else IF (pr == $$(WO~0~1~1)) then p + (#m_pos << $$(WO~1))
     else IF (pr == $$(WO~1~0~0)) then p + (#m_pos << $$(WO~1))
     else IF (pr == $$(WO~1~0~1)) then p + #m_neg
     else IF (pr == $$(WO~1~1~0)) then p + #m_neg
     else p)%kami_expr.

  Definition booth4Step {ty}
             (m_pos m_neg: fullType ty (SyntaxKind (Bit MultBits)))
             (p: Expr ty (SyntaxKind (Bit ((MultBits - 3) + 3))))
    : Expr ty (SyntaxKind (Bit MultBits)) :=
    (booth4Step' m_pos m_neg p (UniBit (Trunc 3 _) p) >> $$(WO~1~0))%kami_expr.

  Fixpoint booth4Steps (cnt: nat)
           {ty} (m_pos m_neg: fullType ty (SyntaxKind (Bit MultBits)))
           (p: fullType ty (SyntaxKind (Bit ((MultBits - 3) + 3))))
           (cont: fullType ty (SyntaxKind (Bit ((MultBits - 3) + 3))) ->
                  ActionT ty Void)
    : ActionT ty Void :=
    match cnt with
    | O => (cont p)%kami_action
    | S n => (LET np <- booth4Step m_pos m_neg #p;
              booth4Steps n m_pos m_neg np cont)%kami_action
    end.

  Definition boothMultRegister :=
    MethodSig "boothMultRegister"(Struct MultInStr): Void.
  Definition boothMultGetResult :=
    MethodSig "boothMultGetResult"(): Struct MultOutStr.

  Definition boothMultiplierImpl :=
    MODULE {
      Register "m_pos" : Bit MultBits <- Default
      with Register "m_neg" : Bit MultBits <- Default
      with Register "p" : Bit MultBits <- Default
      with Register "cnt" : Bit (S MultLogNumPhases) <- Default

      with Method "boothMultRegister"(src: Struct MultInStr): Void :=
        LET m : Bit (pred MultNumBitsExt + 1) <- #src!MultInStr@."multiplicand";
        LET m_neg <- (UniBit (Inv _) #m) + $1;

        LET m_pos : Bit MultBits <-
          BinBit (Concat _ (S MultNumBitsExt)) (UniBit (SignExtendTrunc _ _) #m) $0;
        LET m_neg : Bit MultBits <-
          BinBit (Concat _ (S MultNumBitsExt)) (UniBit (SignExtendTrunc _ _) #m_neg) $0;
        LET r <- #src!MultInStr@."multiplier";
        LET p : Bit MultBits <-
          BinBit (Concat (S MultNumBitsExt) _) $0 (BinBit (Concat _ 1) #r $0);

        (* Handle one bit in advance, in order to deal with other 64 bits 
         * consistently in a rule [boothStep].
         *)
        LET np : Bit MultBits <- boothStep m_pos m_neg #p;
        Write "m_pos" <- #m_pos;
        Write "m_neg" <- #m_neg;
        Write "p" <- #np;

        Write "cnt" : Bit (S MultLogNumPhases) <- $(MultNumPhases);
        Retv

      with Method "boothMultGetResult"(): Struct MultOutStr :=
        Read cnt : Bit MultLogNumPhases <- "cnt";
        Assert (#cnt == $0);

        Read p : Bit MultBits <- "p";
        LET highlowe : Bit (2 * MultNumBitsExt) <-
          UniBit (ConstExtract 1 (2 * MultNumBitsExt) 1) #p;
        LET highlow : Bit (2 * MultNumBits) <-
          UniBit (SignExtendTrunc _ _) #highlowe;
        
        LET high : Bit MultNumBits <- UniBit (TruncLsb _ _) #highlow;
        LET low : Bit MultNumBits <- UniBit (Trunc _ _) #highlow;

        LET ret : Struct MultOutStr <- STRUCT { "high" ::= $$Default; "low" ::= #low };
        Ret #ret
            
      with Rule "boothStep" :=
        Read cnt : Bit MultLogNumPhases <- "cnt";
        Assert (#cnt != $0);

        Read m_pos : Bit MultBits <- "m_pos";
        Read m_neg : Bit MultBits <- "m_neg";
        Read p : Bit MultBits <- "p";

        Write "cnt" <- #cnt - $1;
        
        booth4Steps
          MultNumStepsPerPhase m_pos m_neg p
          (fun np => Write "p" <- #np; Retv)
    }.

  Definition multiplierSpec :=
    MODULE {
      Register "p" : Bit (2 * MultNumBitsExt) <- Default

      with Method "multRegister"(src: Struct MultInStr): Void :=
        LET m : Bit MultNumBitsExt <- #src!MultInStr@."multiplicand";
        LET m_ext : Bit (2 * MultNumBitsExt) <- UniBit (SignExtendTrunc _ _) #m;
        LET r : Bit MultNumBitsExt <- #src!MultInStr@."multiplier";
        LET r_ext : Bit (2 * MultNumBitsExt) <- UniBit (SignExtendTrunc _ _) #m;

        Write "p" <- #m_ext *s #r_ext;
        Retv

      with Method "multGetResult"(): Struct MultOutStr :=
        Read p : Bit (2 * MultNumBitsExt) <- "p";
        LET highlow : Bit (2 * MultNumBits) <- UniBit (SignExtendTrunc _ _) #p;
        
        LET high : Bit MultNumBits <- UniBit (TruncLsb _ _) #highlow;
        LET low : Bit MultNumBits <- UniBit (Trunc _ _) #highlow;

        LET ret : Struct MultOutStr <- STRUCT { "high" ::= #high; "low" ::= #low };
        Ret #ret
    }.

End Multiplier64.


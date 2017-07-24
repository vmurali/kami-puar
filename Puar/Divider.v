Require Import Kami.
Require Import Lib.Indexer Lib.Struct Lib.FMap Lib.Reflection.
Require Import Kami.Tactics Kami.SemFacts.
Require Import Puar.Useful FunctionalExtensionality.

(* Below implements non-restoring division for _unsigned_ integers.
 * Operands should be made unsigned first and the signs should be re-applied
 * after the division.
 * NOTE: the rule for operand signs:
 * when "z = d * q + r", we have "sign(r) = sign(z)" and "|r| < |d|".
 *)
Section Divider64.
  Definition DivLogNumPhases := 3.
  Definition DivNumBitsPerPhase := 8.

  Local Definition DivNumPhases := wordToNat (wones DivLogNumPhases) + 1.
  Local Definition DivNumBits := DivNumPhases * DivNumBitsPerPhase.
  Local Definition DivBits := 2 * DivNumBits + 2.

  Definition DivInStr := STRUCT { "dividend" :: Bit DivNumBits;
                                  "divisor" :: Bit DivNumBits }.
  Definition DivOutStr := STRUCT { "quotient" :: Bit DivNumBits;
                                   "remainder" :: Bit DivNumBits }.

  Definition divRegister := MethodSig "divRegister"(Struct DivInStr): Void.
  Definition divGetResult := MethodSig "divGetResult"(Void): Struct DivOutStr.

  (*! TODO: optimize this step !*)
  Definition divStep {ty}
             (pq: fullType ty (SyntaxKind (Bit (DivNumBits + S DivNumBits))))
             (dr: fullType ty (SyntaxKind (Bit DivNumBits)))
    : Expr ty (SyntaxKind (Bit (DivNumBits + S DivNumBits))) :=
    ((* Step 1: shift *)
      let pq_shift := BinBit (Sll ((DivNumBits + DivNumBits) + 1) _) #pq $$(natToWord 1 1) in
      (* Step 2: add or subtract *)
      let pq_shift_msb := UniBit (TruncLsb _ 1) pq_shift in
      let pq_shift_p := (IF (pq_shift_msb == $0)
                         then pq_shift - (BinBit (Concat _ (S DivNumBits)) #dr $0)
                         else pq_shift + (BinBit (Concat _ (S DivNumBits)) #dr $0)) in
      (* Step 3: set the quotient bit, which is LSB here *)
      let pq_shift_p_msb := UniBit (TruncLsb _ 1) pq_shift_p in
      IF (pq_shift_p_msb == $0)
      then pq_shift_p + $1
      else pq_shift_p
    )%kami_expr.
  
  Fixpoint divSteps (cnt: nat)
           {ty} (pq: fullType ty (SyntaxKind (Bit (DivNumBits + S DivNumBits))))
           (dr: fullType ty (SyntaxKind (Bit DivNumBits)))
           (cont: fullType ty (SyntaxKind (Bit (DivNumBits + S DivNumBits))) ->
                  ActionT ty Void)
    : ActionT ty Void :=
    match cnt with
    | O => (cont pq)%kami_action
    | S n => (LET npq <- divStep pq dr;
              divSteps n npq dr cont)%kami_action
    end.

  Definition nrDivRegister :=
    MethodSig "nrDivRegister"(Struct DivInStr): Void.
  Definition nrDivGetResult :=
    MethodSig "nrDivGetResult"(): Struct DivOutStr.

  Definition nrDividerImpl :=
    MODULE {
      Register "pq" : Bit (DivNumBits + S DivNumBits) <- Default
      with Register "dr" : Bit DivNumBits <- Default
      with Register "cnt" : Bit (S DivLogNumPhases) <- Default

      with Method "nrDivRegister"(src: Struct DivInStr): Void :=
        LET dividend : Bit DivNumBits <- #src!DivInStr@."dividend";
        LET divisor : Bit DivNumBits <- #src!DivInStr@."divisor";

        Write "pq" : Bit (DivNumBits + S DivNumBits) <- UniBit (ZeroExtendTrunc _ _) #dividend;
        Write "dr" <- #divisor;
        Write "cnt" : Bit (S DivLogNumPhases) <- $(DivNumPhases);
        Retv

      with Method "nrDivGetResult"(): Struct DivOutStr :=
        Read cnt : Bit DivLogNumPhases <- "cnt";
        Assert (#cnt == $0);

        Read pq : Bit (DivNumBits + S DivNumBits) <- "pq";
        Read dr : Bit DivNumBits <- "dr";
        
        LET p : Bit (DivNumBits + 1) <- UniBit (TruncLsb _ _) #pq;
        LET q : Bit DivNumBits <- UniBit (Trunc _ _) #pq;

        LET p_msb <- UniBit (TruncLsb _ 1) #p;
        LET p_ls : Bit DivNumBits <- UniBit (Trunc _ _) #p;
        LET rem : Bit DivNumBits <- (IF (#p_msb == $0)
                                     then #p_ls
                                     else #p_ls + #dr);
        
        LET ret : Struct DivOutStr <- STRUCT { "quotient" ::= #q;
                                               "remainder" ::= #rem
                                             };
        Ret #ret
            
      with Rule "divStep" :=
        Read cnt : Bit DivLogNumPhases <- "cnt";
        Assert (#cnt != $0);

        Read pq : Bit (DivNumBits + S DivNumBits) <- "pq";
        Read dr : Bit DivNumBits <- "dr";
        
        divSteps
          DivNumBitsPerPhase pq dr
          (fun npq => Write "pq" <- #npq; Retv)
    }.

  Definition dividerSpec :=
    MODULE {
      Register "quotient" : Bit DivNumBits <- Default
      with Register "remainder" : Bit DivNumBits <- Default
                         
      with Method "divRegister"(src: Struct DivInStr): Void :=
        LET m : Bit DivNumBits <- #src!DivInStr@."dividend";
        LET r : Bit DivNumBits <- #src!DivInStr@."divisor";

        Write "quotient" <- #m / #r;
        Write "remainder" <- BinBit (Rem _ SignSS) #m #r;
        Retv

      with Method "divGetResult"(): Struct DivOutStr :=
        Read quotient : Bit DivNumBits <- "quotient";
        Read remainder : Bit DivNumBits <- "remainder";

        LET ret : Struct DivOutStr <- STRUCT { "quotient" ::= #quotient;
                                               "remainder" ::= #remainder };
        Ret #ret
    }.
  
End Divider64.


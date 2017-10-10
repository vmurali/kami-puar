Require Import Kami.
Require Import Lib.Indexer Lib.Struct Lib.FMap Lib.Reflection.
Require Import Kami.Tactics Kami.SemFacts.
Require Import Puar.Useful FunctionalExtensionality.

(* Below implements non-restoring division for _unsigned_ integers.
 * Operands should be made unsigned first and the signs should be re-applied
 * after the division.
 *)
Section Divider64.
  Definition DivLogNumPhases := 3.
  Definition DivNumBitsPerPhase := 8.

  Local Definition DivNumPhases := wordToNat (wones DivLogNumPhases) + 1.
  Local Definition DivNumBits := DivNumPhases * DivNumBitsPerPhase.
  Local Definition DivBits := DivNumBits + (S DivNumBits).

  Definition DivInStr := STRUCT { "dividend" :: Bit DivNumBits;
                                  "divisor" :: Bit DivNumBits }.
  Definition DivOutStr := STRUCT { "quotient" :: Bit DivNumBits;
                                   "remainder" :: Bit DivNumBits }.

  Definition divRegister := MethodSig "divRegister"(Struct DivInStr): Void.
  Definition divGetResult := MethodSig "divGetResult"(Void): Struct DivOutStr.

  Definition nrDivStep {ty}
             (p: fullType ty (SyntaxKind (Bit DivBits)))
             (div: fullType ty (SyntaxKind (Bit DivNumBits)))
    : Expr ty (SyntaxKind (Bit (DivNumBits + S DivNumBits))) :=
    ((* Step 1: shift 1-bit *)
      let pq_shift := BinBit (Sll ((DivNumBits + DivNumBits) + 1) _) #p $$(natToWord 1 1) in
      (* Step 2: add or subtract *)
      (* Step 3: set the quotient bit, which is a LSB here *)
      let pq_shift_msb := UniBit (TruncLsb _ 1) pq_shift in
      IF (pq_shift_msb == $0)
      then pq_shift - (BinBit (Concat _ (S DivNumBits)) #div $1 (* lsb to 1 *))
      else pq_shift + (BinBit (Concat _ (S DivNumBits)) #div $0 (* lsb to 0 *))
    )%kami_expr.

  Fixpoint nrDivSteps (cnt: nat)
           {ty} (p: fullType ty (SyntaxKind (Bit (DivNumBits + S DivNumBits))))
           (div: fullType ty (SyntaxKind (Bit DivNumBits)))
           (cont: fullType ty (SyntaxKind (Bit (DivNumBits + S DivNumBits))) ->
                  ActionT ty Void)
    : ActionT ty Void :=
    match cnt with
    | O => (cont p)%kami_action
    | S n => (LET npq <- nrDivStep p div;
              nrDivSteps n npq div cont)%kami_action
    end.

  Definition nrDivPull := MethodSig "nrDivPull"(): Struct DivInStr.
  Definition nrDivPush := MethodSig "nrDivPush"(Struct DivOutStr): Void.

  (* Positive-negative digit {0 |-> -1, 1 |-> 1} number 
   * to the corresponding binary number. *)
  Definition pn2bin {ty n} (w: fullType ty (SyntaxKind (Bit n)))
    : Expr ty (SyntaxKind (Bit n)) :=
    (#w - (UniBit (Inv _) #w - $1))%kami_expr.

  Definition nrDividerImpl :=
    MODULE {
      Register "pq" : Bit (DivNumBits + S DivNumBits) <- Default
      with Register "dr" : Bit DivNumBits <- Default
      with Register "cnt" : Bit (S DivLogNumPhases) <- Default

      with Rule "nrDivRegister" :=
        Call src <- nrDivPull();
        
        LET dividend : Bit DivNumBits <- #src!DivInStr@."dividend";
        LET divisor : Bit DivNumBits <- #src!DivInStr@."divisor";

        Write "pq" : Bit (DivNumBits + S DivNumBits) <- UniBit (ZeroExtendTrunc _ _) #dividend;
        Write "dr" <- #divisor;
        Write "cnt" : Bit (S DivLogNumPhases) <- $(DivNumPhases);
        Retv

      with Rule "nrDivGetResult" :=
        Read cnt : Bit DivLogNumPhases <- "cnt";
        Assert (#cnt == $0);

        Read pq : Bit (DivNumBits + S DivNumBits) <- "pq";
        Read dr : Bit DivNumBits <- "dr";
        
        LET rem : Bit (DivNumBits + 1) <- UniBit (TruncLsb _ _) #pq;
        LET rem_msb <- UniBit (TruncLsb _ 1) #rem;
        LET q_pn : Bit DivNumBits <- UniBit (Trunc _ _) #pq;
        LET q_bin : Bit DivNumBits <- pn2bin q_pn;

        (* A final restoring, if necessary *)
        LET rem_rst : Bit DivNumBits <-
          (IF (#rem_msb == $0)
           then UniBit (Trunc _ _) #rem
           else (UniBit (Trunc _ _) (#rem + (UniBit (SignExtendTrunc _ _) #dr))));
        
        LET q_rst : Bit DivNumBits <- (IF (#rem_msb == $0)
                                       then #q_bin
                                       else #q_bin - $1);

        Call nrDivPush(STRUCT { "quotient" ::= #q_rst;
                                "remainder" ::= #rem_rst });
        Retv
            
      with Rule "divStep" :=
        Read cnt : Bit DivLogNumPhases <- "cnt";
        Assert (#cnt != $0);

        Read pq : Bit (DivNumBits + S DivNumBits) <- "pq";
        Read dr : Bit DivNumBits <- "dr";
        
        nrDivSteps
          DivNumBitsPerPhase pq dr
          (fun npq => Write "pq" <- #npq; Retv)
    }.

  Definition dividerSpec :=
    MODULE {
      Register "m" : Bit DivNumBits <- Default
      with Register "r" : Bit DivNumBits <- Default

      with Rule "divRegister" :=
        Call src <- nrDivPull();
        LET m : Bit DivNumBits <- #src!DivInStr@."dividend";
        LET r : Bit DivNumBits <- #src!DivInStr@."divisor";
        Write "m" <- #m;
        Write "r" <- #r;
        Retv

      with Rule "divGetResult" :=
        Read m : Bit DivNumBits <- "m";
        Read r : Bit DivNumBits <- "r";
        LET quotient <- #m / #r;
        LET remainder <- BinBit (Rem _ true) #m #r;

        Call nrDivPush(STRUCT { "quotient" ::= #quotient;
                                "remainder" ::= #remainder });
        Retv
    }.

  (*! Correctness of the divider *)

  (* Inductive NrDivInv. *)

  (* Record NrDividerInv (o: RegsT): Prop. *)

  (* Ltac nrDivider_old := *)
  (*   repeat match goal with *)
  (*          | [H: NrDividerInv _ |- _] => destruct H *)
  (*          end; *)
  (*   kinv_red. *)

  (* Ltac nrDivider_new := *)
  (*   econstructor; (* let's prove that the invariant holds for the next state *) *)
  (*   try (findReify; (reflexivity || eassumption); fail); *)
  (*   kinv_red; (* unfolding invariant definitions *) *)
  (*   repeat (* cheaper than "intuition" *) *)
  (*     (match goal with *)
  (*      | [ |- _ /\ _ ] => split *)
  (*      end); *)
  (*   try eassumption; intros; try reflexivity; *)
  (*   intuition kinv_simpl; intuition idtac. *)

  (* Lemma nrDividerInv_ok': *)
  (*   forall init n ll, *)
  (*     init = initRegs (getRegInits nrDividerImpl) -> *)
  (*     Multistep nrDividerImpl init n ll -> *)
  (*     NrDividerInv n. *)
  (* Proof. *)
  (* induction 2; intros. *)
  
  (* - nrDividerInv_old. *)
  (*   unfold getRegInits, fst, nrDividerImpl, projT1. *)
  (*   nrDividerInv_new. *)

  (* - kinvert; [mred|mred| | |]. *)
  (* Qed. *)
  
  (* Lemma nrDividerInv_ok: *)
  (*   forall o, *)
  (*     reachable o nrDividerImpl -> *)
  (*     NrDividerInv o. *)
  (* Proof. *)
  (*   intros; inv H; inv H0. *)
  (*   eapply nrDividerInv_ok'; eauto. *)
  (* Qed. *)
  
  (* Local Definition thetaR (ir sr: RegsT): Prop. *)
  (* Proof. *)
  (*   exact False. *)
  (* Defined. *)
  (* Hint Unfold thetaR: MapDefs. *)

  (* Local Notation "'_STRUCT_'" := (fun i : Fin.t _ => _). *)

  (* Theorem divider_ok: nrDividerImpl <<== dividerSpec. *)
  (* Proof. *)
  (*   kdecomposeR_nodefs thetaR. *)
  (*   kinv_add nrDividerInv_ok. *)
  (*   kinvert. *)
  (* Qed. *)

End Divider64.


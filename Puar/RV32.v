Require Import Kami Puar.Processor Puar.Useful.

Set Implicit Arguments.
Set Asymmetric Patterns.

Open Scope string.
Notation fst := "fst".
Notation snd := "snd".
Close Scope string.

Definition Pair (A B: Kind) := STRUCT { fst :: A ; snd :: B }.

Section RV32.
  Definition XlenBytes := 4.
  Definition VAddrSz := 32.
  Variable PAddrSz: nat.

  Definition RIndexSz := 5.

  Definition VAddr := Bit VAddrSz.
  Definition PAddr := Bit PAddrSz.
  Definition Inst := Bit 32.

  Definition Mode := Bit 2.

  Definition BtbSz := 10.
  Definition BpSz := 20.

  Definition BtbTagSz := VAddrSz - (BtbSz + 2).
  Definition BtbDataSz := VAddrSz - 2.
  Definition BtbData := Bit BtbDataSz.

  Definition BtbState := Vector (optT (Struct (Pair (Bit BtbTagSz) BtbData))) BtbSz.
  Definition BpState := Vector (Bit 2) BpSz.
  
  Variable PcInit: ConstT VAddr.
  Definition RegFileInit := getDefaultConst (Vector (Data XlenBytes) RIndexSz).
  Definition BtbInit := getDefaultConst BtbState.
  Definition BpInit := getDefaultConst BpState.

  Definition Data := ltac:(let y := eval simpl in (Bit (8 * XlenBytes)) in exact y).

  Open Scope string.
  Notation bInstAddr := "bInstAddr".
  Notation bAddr := "bAddr".
  Notation extF := "extF".
  Notation extM := "extM".
  Notation ext64 := "ext64".
  Notation extC := "extC".
  Notation other := "other".
  Close Scope string.

  Variable FpuException : Kind.
  
  Definition ExecException :=
    STRUCT {
        bInstAddr :: Bool ;
        bAddr :: Bool ;
        extF :: Bool ;
        ext64 :: Bool ;
        extC :: Bool ;
        other :: Bool }.
          
  Notation Exec := (Exec XlenBytes VAddr (Struct ExecException)).

  Notation "a $[ i :>: j ]@ w":=
    (UniBit
       (ConstExtract
          j
          (* (ltac:(let y := eval cbv in (i + 1 - j)%nat in exact y)) *)
          (i + 1 - j)%nat
          (* (ltac:(let y := eval cbv in (31 - i)%nat in exact y)) *)
          (w - 1 - i)%nat
       ) a) (at level 12).
  
  Notation "{ a , b }" := (BinBit (Concat _ _) a b).

  Open Scope kami_expr.
  Definition opcode ty (inst: ty Inst) :=
    #inst$[6 :>: 0]@32.

  Definition op1_0 ty (inst: ty Inst) :=
    #inst$[1 :>: 0]@32.

  Definition op4_2 ty (inst: ty Inst) :=
    #inst$[4 :>: 2]@32.

  Definition op6_5 ty (inst: ty Inst) :=
    #inst$[6 :>: 5]@32.
  
  Definition funct3 ty (inst: ty Inst) :=
    #inst$[14 :>: 12]@32.

  Definition funct7 ty (inst: ty Inst) :=
    #inst$[31 :>: 25]@32.

  Definition rd ty (inst: ty Inst) :=
    #inst$[11 :>: 7]@32.

  Definition rs1 ty (inst: ty Inst) :=
    #inst$[19 :>: 15]@32.

  Definition rs2 ty (inst: ty Inst) :=
    #inst$[24 :>: 20]@32.

  Definition iImm ty (inst: ty Inst) :=
    UniBit (SignExtendTrunc _ 32) {#inst$[31 :>: 31]@32,
                                   {#inst$[30 :>: 25]@32,
                                    {#inst$[24 :>: 21]@32,
                                     #inst$[20 :>: 20]@32}}}.
                                         
  Definition sImm ty (inst: ty Inst) :=
    UniBit (SignExtendTrunc _ 32) {#inst$[31 :>: 31]@32,
                                   {#inst$[30 :>: 25]@32,
                                    {#inst$[11 :>: 8]@32,
                                     #inst$[7 :>: 7]@32}}}.
                                         
  Definition bImm ty (inst: ty Inst) :=
    UniBit (SignExtendTrunc _ 32) {{#inst$[31 :>: 31]@32,
                                    #inst$[7 :>: 7]@32},
                                   {#inst$[30 :>: 25]@32,
                                    {#inst$[11 :>: 8]@32,
                                     #inst$[7 :>: 7]@32}}}.
                                         
  Definition uImm ty (inst: ty Inst): (Bit 32) @ ty :=
    {#inst$[31 :>: 31]@32,
     {#inst$[30 :>: 20]@32,
      {#inst$[19 :>: 12]@32,
       ($ 0: (Bit 12) @ ty) }}}.

  Definition jImm ty (inst: ty Inst) :=
    UniBit (SignExtendTrunc _ 32) {{#inst$[31 :>: 31]@32,
                                    {#inst$[19 :>: 12]@32,
                                     #inst$[20 :>: 20]@32}},
                                   {#inst$[30 :>: 25]@32,
                                    {#inst$[24 :>: 21]@32,
                                     ($ 0: (Bit 1) @ ty)}}}.

  Definition alu ty (d1 d2: Data @ ty) (f3: (Bit 3) @ ty) (f7: Bool @ ty) :=
    (IF (f3 == $ 0)
     then (IF f7
           then d1 + d2
           else d1 - d2)
     else (IF (f3 == $ 1)
           then (d1 << (d2$[4 :>: 0]@32))
           else (IF (f3 == $ 2)
                 then (IF (d1 < d2) then $ 1 else $ 0)
                 else (IF (f3 == $ 3)
                       then (IF (BinBitBool (Slt _) d1 d2) then $ 1 else $ 0)
                       else (IF (f3 == $ 4)
                             then d1 ~+ d2
                             else (IF (f3 == $ 5)
                                   then (IF f7
                                         then d1 >> (d2$[4 :>: 0]@32)
                                         else d1 ~>> (d2$[4 :>: 0]@32))
                                   else (IF (f3 == $ 6)
                                         then d1 ~| d2
                                         else (IF (f3 == $ 7)
                                               then d1 ~& d2
                                               else $ 0)))))))).

  Local Definition getExecException ty (pc: ty VAddr) (inst: ty Inst) (nextPcVal: VAddr @ ty) :=
    STRUCT {
        bInstAddr ::= #pc$[1 :>: 0]@32 != $ 0 ;
        bAddr ::= nextPcVal$[1 :>: 0]@32 != $ 0 ;
        extF ::= ((op4_2 _ inst == $ 1 && (op6_5 _ inst)$[1 :>: 1]@2 == $ 0) ||
                  (op4_2 _ inst == $ 4 && op6_5 _ inst == $ 2) ||
                  ((op4_2 _ inst)$[2 :>: 2]@3 == $ 0 && op6_5 _ inst == $ 2)) ;
        ext64 ::= op4_2 _ inst == $ 6 && op6_5 _ inst$[1 :>: 1]@2 == $ 0 ;
        extC ::= op1_0 _ inst != $ 3 ;
        other ::= ((op4_2 _ inst == $ 2 && op6_5 _ inst != $ 2)
                     ||
                     (((op4_2 _ inst)$[2 :>: 2]@3 == $ 1)
                        && ((((op4_2 _ inst)$[1 :>: 1]@3 == $ 1)
                               || ((op4_2 _ inst)$[0 :>: 0]@3 == $ 1))
                              && (op6_5 _ inst)$[1 :>: 1]@2 == $ 1)) ||
                     op4_2 _ inst == $ 7) }.

  (*
    OP-IMM: 00, 100
    OP:     01, 100, funct7[5]
    AUIPC:  00, 101
    LUI:    01, 101
    JALR:   11, 001
    JAL:    11, 011
    Branch: 11, 000
    LoadS:  00, 000, funct3[2] 0
    LoadU:  00, 000, funct3[2] 1
    Store:  01, 000
    AMO:    01, 011
   *)
  Definition execNotLongLatFn ty (pc: ty VAddr) (inst: ty Inst) (src1 src2: ty Data)
    : ((Struct Exec) @ ty) :=
    let nextPcVal :=
        (#pc +
         (IF (op4_2 _ inst)$[1 :>: 0]@3 == $ 0
          then (IF ((funct3 _ inst == $ 0 && #src1 == #src2) ||
                    (funct3 _ inst == $ 1 && #src1 != #src2) ||
                    (funct3 _ inst == $ 4 && BinBitBool (Slt _) #src1 #src2) ||
                    (funct3 _ inst == $ 5 &&
                                        !(BinBitBool (Slt _) #src2 #src1)) ||
                    (funct3 _ inst == $ 6 && (#src1 < #src2)) ||
                    (funct3 _ inst == $ 7 && (#src1 >= #src2)))
                then bImm _ inst
                else$ 4)
          else (IF (op4_2 _ inst)$[1 :>: 1]@3 == $ 0
                then #src1 + iImm _ inst
                else jImm _ inst)
        )) in
        STRUCT {
          (*
            ALU operations:
            OP-IMM: src1 op iImm, 00, 100
            OP: src1 op src2,     01, 100
            AUIPC: pc + uImm,     00, 101
            LUI: uImm,            01, 101
            JAL, JALR: pc + 4,    11, 0x1
           *)
        data ::=
             alu
             (IF (op4_2 _ inst)$[0 :>: 0]@3 == $ 1
              then (IF (op6_5 _ inst)$[0 :>: 0]@2 == (op6_5 _ inst)$[1 :>: 1]@2
                    then #pc
                    else $ 0)
              else #src1)
             (IF (op4_2 _ inst)$[0 :>: 0]@3 == $ 0
              then (IF (op6_5 _ inst)$[0 :>: 0]@2 == $ 0
                    then iImm _ inst
                    else #src2)
              else (IF (op6_5 _ inst)$[1 :>: 1]@2 == $ 0
                    then uImm _ inst
                    else $ 4))
             (funct3 _ inst)
             ((funct7 _ inst)$[5 :>: 5]@7 == $ 0) ;

        (*
          Memory operations:
          Load (signed), Store: src1 + iImm, 0x, 000, funct3[2] 0
          Load (unsigned): src1 + sImm,      00, 000, funct3[2] 1
          AMO: src1,                         01, 011
         *)
        memVAddr ::=
             (#src1 + (IF (op4_2 _ inst)$[0 :>: 0]@3 == $ 0
                       then (IF (funct3 _ inst)$[2 :>: 2]@2 == $ 0
                             then sImm _ inst
                             else iImm _ inst)
                       else $ 0)) ;

        (*
          Exception:
          JAL, JALR: instruction address misaligned
          AMO: misaligned address
          _: illegal instruction
         *)
        exception ::= getExecException pc inst nextPcVal ;

        (*
          Branch operations:
          Branch: pc + bImm,      11, 000
          JALR: pc + src1 + iImm, 11, 001
          JAL: pc + jImm,         11, 011
         *)
        nextPc ::= nextPcVal
        }.

  Local Definition isLongLat ty (pc: ty VAddr) (inst: ty Inst) (nextPcVal: VAddr @ ty) :=
    ((getExecException pc inst nextPcVal)!ExecException@.extF).

  Definition isNotLongLat ty (pc: ty VAddr) (inst: ty Inst) (nextPcVal: VAddr @ ty) :=
    ! (isLongLat pc inst nextPcVal).
  
  Definition execLongLatFn ty (pc: ty VAddr) (inst: ty Inst) (src1 src2: ty Data)
    : ((Struct Exec) @ ty) :=
    STRUCT {
        data ::= $$ Default ;
        memVAddr ::= $$ Default ;
        exception ::= getExecException pc inst ($$ Default) ;
        nextPc ::= $$ Default }.

  Definition useSrc1 ty (inst: ty Inst) :=
    (op4_2 _ inst == $ 0 && op6_5 _ inst != $ 2)
    || (op4_2 _ inst == $ 1 && op6_5 _ inst == $ 3)
    || (op4_2 _ inst == $ 4 && op6_5 _ inst == $ 3 && (funct3 _ inst)$[2 :>: 2]@3 == $ 0).

  Definition useSrc2 ty (inst: ty Inst) :=
    (op4_2 _ inst == $ 0 && (op6_5 _ inst)$[0 :>: 0]@2 != $ 1)
    || (op4_2 _ inst == $ 4 && op6_5 _ inst == $ 1).

  Definition useDst ty (inst: ty Inst) :=
    (rd _ inst != $ 0)
      && ((op4_2 _ inst == $ 0 && op6_5 _ inst == $ 0)
          || (op4_2 _ inst == $ 1 && op6_5 _ inst == $ 3)
          || (op4_2 _ inst == $ 3 && op6_5 _ inst == $ 3)
          || (op4_2 _ inst == $ 4 && op6_5 _ inst != $ 2)
          || (op4_2 _ inst == $ 5 && (op6_5 _ inst)$[1 :>: 1]@2 == $ 0)).

  Definition isLd ty (inst: ty Inst) := op4_2 _ inst == $ 0 && op6_5 _ inst == $ 0.
  Definition isSt ty (inst: ty Inst) := op4_2 _ inst == $ 0 && op6_5 _ inst == $ 1.

  Definition next ty (pc: ty VAddr) := #pc + $ 4.  

  (* Definition getNextBtb ty (btbState: ty BtbState) (pc: ty VAddr) := *)
  (*   let btbIndex := UniBit (Trunc BtbSz 2) *)
  (*                          (UniBit (Trunc (BtbSz + 2) (VAddrSz - (BtbSz + 2))) #pc) in *)
  (*   (IF #btbState@[btbIndex]!(opt (Struct (Pair (Bit BtbTagSz) BtbData)))@.valid && *)
  (*       (#btbState@[btbIndex]!(opt (Struct (Pair (Bit BtbTagSz) BtbData)))@.data! *)
  (*         (Pair (Bit BtbTagSz) BtbData)@.fst == *)
  (*        (UniBit (TruncLsb (BtbSz + 2) (VAddrSz - (BtbSz + 2))) #pc)) *)
  (*    then {#btbState@[btbIndex]!(opt (Struct (Pair (Bit BtbTagSz) BtbData)))@.data! *)
  (*           (Pair (Bit BtbTagSz) BtbData)@.snd, ($$ Default) : (Bit 2) @ ty } *)
  (*    else #pc + $ 4). *)

  (* Definition updBtb ty (btbState: ty BtbState) (pc: ty VAddr) (isException: ty Bool) *)
  (*            (nextPcVal: ty VAddr) := *)
  (*   let btbIndex := UniBit (Trunc BtbSz 2) *)
  (*                          (UniBit (Trunc (BtbSz + 2) (VAddrSz - (BtbSz + 2))) #pc) in *)
  (*   #btbState@[btbIndex <- *)
  (*                       (IF (#nextPcVal != (#pc + $ 4)) *)
  (*                        then STRUCT { *)
  (*                                 valid ::= $$ true; *)
  (*                                 data ::= STRUCT { *)
  (*                                        fst ::= UniBit (TruncLsb (BtbSz + 2) *)
  (*                                                                 (VAddrSz - (BtbSz + 2))) #pc; *)
  (*                                        snd ::= UniBit (TruncLsb 2 BtbDataSz) #nextPcVal } *)
  (*                               } *)
  (*                        else STRUCT { *)
  (*                                 valid ::= $$ false; *)
  (*                                 data ::= $$ Default *)
  (*                               } *)
  (*             )]. *)

  (* Definition getNextBp ty (bpState: ty BpState) (pc: ty VAddr) := *)
  (*   let bpIndex := UniBit (Trunc BpSz 2) *)
  (*                          (UniBit (Trunc (BpSz + 2) (VAddrSz - (BpSz + 2))) #pc) in *)
  (*   (IF #bpState@[bpIndex]!(opt (Struct (Pair (Bit BpTagSz) BpData)))@.valid && *)
  (*       (#bpState@[bpIndex]!(opt (Struct (Pair (Bit BpTagSz) BpData)))@.data! *)
  (*         (Pair (Bit BpTagSz) BpData)@.fst == *)
  (*        (UniBit (TruncLsb (BpSz + 2) (VAddrSz - (BpSz + 2))) #pc)) *)
  (*    then {#bpState@[bpIndex]!(opt (Struct (Pair (Bit BpTagSz) BpData)))@.data! *)
  (*           (Pair (Bit BpTagSz) BpData)@.snd, ($$ Default) : (Bit 2) @ ty } *)
  (*    else #pc + $ 4). *)

  (* Definition updBp ty (bpState: ty BpState) (pc: ty VAddr) (isException: ty Bool) *)
  (*            (nextPcVal: ty VAddr) := *)
  (*   let bpIndex := UniBit (Trunc BpSz 2) *)
  (*                          (UniBit (Trunc (BpSz + 2) (VAddrSz - (BpSz + 2))) #pc) in *)
  (*   #bpState@[bpIndex <- *)
  (*                       (IF (#nextPcVal != (#pc + $ 4)) *)
  (*                        then STRUCT { *)
  (*                                 valid ::= $$ true; *)
  (*                                 data ::= STRUCT { *)
  (*                                        fst ::= UniBit (TruncLsb (BpSz + 2) *)
  (*                                                                 (VAddrSz - (BpSz + 2))) #pc; *)
  (*                                        snd ::= UniBit (TruncLsb 2 BpDataSz) #nextPcVal } *)
  (*                               } *)
  (*                        else STRUCT { *)
  (*                                 valid ::= $$ false; *)
  (*                                 data ::= $$ Default *)
  (*                               } *)
  (*             )]. *)
  Close Scope kami_expr.
End RV32.

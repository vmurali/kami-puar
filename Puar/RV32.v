Require Import Kami Puar.Processor Puar.Useful.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section Riscv.
  Definition XlenBytes := 4.
  Variable VAddrSz PAddrSz: nat.

  Definition RIndexSz := 5.

  Definition VAddr := Bit VAddrSz.
  Definition PAddr := Bit PAddrSz.
  Definition Inst := Bit 32.

  Definition Mode := Bit 2.
  
  Variable BtbSz BpSz: nat.

  Definition BtbState := Vector (optT VAddr) BtbSz.
  Definition BpState := Vector (Bit 2) BpSz.
  
  Variable PcInit: ConstT VAddr.
  Definition RegFileInit := getDefaultConst (Vector (Data XlenBytes) RIndexSz).
  Definition BtbInit := getDefaultConst BtbState.
  Definition BpInit := getDefaultConst BpState.

  Definition Data := ltac:(let y := eval simpl in (Bit (8 * XlenBytes)) in exact y).

  Open Scope string.
  Notation fpu := "fpu".
  Notation baddr := "baddr".
  Notation inst := "inst".
  Close Scope string.

  Variable FpuException : Kind.
  
  Definition ExecException :=
    STRUCT {
        fpu :: FpuException ;
        baddr :: Bool ;
        inst :: Bool }.
          
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
  
  Definition op6_2 ty (inst: ty Inst) :=
    #inst$[6 :>: 2]@32.
  
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

  Definition execFn ty (inst: ty Inst) (src1 src2: ty Data):
    ((Struct Exec) @ ty) :=
    STRUCT {
        data ::=
          (IF (op4_2 _ inst) == $ 4
           then alu #src1 (IF ((op6_5 _ inst) $[0 :>: 0]@ 2) == $ 0
                           then (iImm _ inst)
                           else #src2) (funct3 _ inst) (((funct7 _ inst)$[5 :>: 5]@7) == $ 1)
           else $ 0) ;
        memVAddr ::= $ 0 ;
        exception ::= none ;
        nextPc ::= $ 0 }.
  
                   then 
               then Ret $ 0
               else (
                   IF op4_2(inst) == $ 1
                   then Ret $ 0
                   else (
                       IF op4_2(inst) 
                            
    (LET opcode : Opcode <- UniBitOp _ _ (Trunc _ _) #inst;
     Ret $$ Default)%kami_action.
    If (inst 
    
  
  
  Close Scope kami_expr.






  


  Variable NumDataBytes RIndexSz: nat.
  Variable VAddr PAddr Inst MemRq CState Mode MemException ExecException FinalException Interrupts
           CmdNonUser CmdInst CmdData: Kind.
  Definition Data := Bit (8 * NumDataBytes).
  Variable PcInit: ConstT VAddr.
  Variable RegFileInit: ConstT (Vector Data RIndexSz).
  Variable CStateInit: ConstT CState.
  Variable ModeInit: ConstT Mode.

  Variable BtbState BpState: Kind.
  Variable BtbStateInit: ConstT BtbState.
  Variable BpStateInit: ConstT BpState.

  Notation RIndex := (Bit RIndexSz).

  Variable getSrc1: forall ty, ty Inst -> RIndex @ ty.
  Variable getSrc2: forall ty, ty Inst -> RIndex @ ty.
  Variable useSrc1: forall ty, ty Inst -> Bool @ ty.
  Variable useSrc2: forall ty, ty Inst -> Bool @ ty.
  Variable useDst: forall ty, ty Inst -> Bool @ ty. (* This folds in whether dst is zero or not *)
  Variable getDst: forall ty, ty Inst -> RIndex @ ty.

  Definition Exec := STRUCT
                       { data :: Data;
                         memVAddr :: VAddr;
                         exception :: optT ExecException;
                         nextPc :: VAddr
                       }.
  
  Variable execFn: forall ty, ty Inst -> ty Data -> ty Data ->
                              (Struct Exec) @ ty.
  
  Definition CExec := STRUCT
                        { cState :: CState;
                          mode :: Mode;
                          exception :: optT FinalException;
                          nextPc :: VAddr;
                          cmdInst :: CmdInst;
                          cmdData :: CmdData;
                          cmdNonUser :: CmdNonUser
                        }.
  
  Definition VToPRp := STRUCT
                         { pAddr :: PAddr;
                           mode :: Mode;
                           exception :: optT MemException
                         }.
  
  Variable cExec:
    forall ty,
      ty VAddr -> ty (Struct VToPRp) -> ty Inst ->
      ty VAddr -> ty (optT ExecException) -> ty VAddr ->
      ty (optT (Struct VToPRp)) ->
      ty Mode -> ty CState -> ty Interrupts -> (Struct CExec) @ ty.

  Variable isLd: forall ty, ty Inst -> Bool @ ty.
  Variable isSt: forall ty, ty Inst -> Bool @ ty.

  Variable getNextBtb: forall ty, ty BtbState -> ty VAddr -> VAddr @ ty.
  Variable updBtb: forall ty, ty BtbState -> ty VAddr -> ty VAddr -> BtbState @ ty.

  Variable getBp: forall ty, ty BpState -> ty VAddr -> ty Inst -> VAddr @ ty.
  Variable updBp: forall ty, ty BtbState -> ty VAddr -> ty Inst -> ty Bool ->
                             BpState @ ty.

  Variable useSrc1Means: forall i, evalExpr (useSrc1 type i) = false ->
                                   forall s1 s1' s2,
                                     evalExpr (execFn type i s1 s2) =
                                     evalExpr (execFn type i s1' s2).
  Variable useSrc2Means: forall i, evalExpr (useSrc2 type i) = false ->
                                   forall s1 s2 s2',
                                     evalExpr (execFn type i s1 s2) =
                                     evalExpr (execFn type i s1 s2').
            
  
  Notation isLdSt ty inst := (isLd ty inst || isSt ty inst)%kami_expr.
  Notation isNm ty inst := (!(isLdSt ty inst))%kami_expr.


  Variable createMemRq: forall ty, ty Inst -> ty PAddr -> ty Data -> MemRq @ ty.

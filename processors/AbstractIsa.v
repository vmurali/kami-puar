Require Import Kami.
Require Import Ex.MemTypes.

Set Implicit Arguments.

Section AbstractIsa.
  Variables (addrSize dataBytes rfIdx csrIdx: nat).

  Section Decode.

    Definition IType := Bit 4.
    Definition iTypeUnsupported: ConstT IType := WO~0~0~0~0.
    Definition iTypeAlu: ConstT IType := WO~0~0~0~1.
    Definition iTypeLd: ConstT IType := WO~0~0~1~0.
    Definition iTypeSt: ConstT IType := WO~0~0~1~1.
    Definition iTypeJ: ConstT IType := WO~0~1~0~0.
    Definition iTypeJr: ConstT IType := WO~0~1~0~1.
    Definition iTypeBr: ConstT IType := WO~0~1~1~0.
    Definition iTypeCsrr: ConstT IType := WO~0~1~1~1.
    Definition iTypeCsrw: ConstT IType := WO~1~0~0~0.
    Definition iTypeAuipc: ConstT IType := WO~1~0~0~1.

    Definition AluFunc := Bit 4.
    Definition aluAdd: ConstT AluFunc := WO~0~0~0~0.
    Definition aluSub: ConstT AluFunc := WO~0~0~0~1.
    Definition aluAnd: ConstT AluFunc := WO~0~0~1~0.
    Definition aluOr: ConstT AluFunc := WO~0~0~1~1.
    Definition aluXor: ConstT AluFunc := WO~0~1~0~0.
    Definition aluSlt: ConstT AluFunc := WO~0~1~0~1.
    Definition aluSltu: ConstT AluFunc := WO~0~1~1~0.
    Definition aluSll: ConstT AluFunc := WO~0~1~1~1.
    Definition aluSra: ConstT AluFunc := WO~1~0~0~0.
    Definition aluSrl: ConstT AluFunc := WO~1~0~0~1.

    Definition BrFunc := Bit 3.
    Definition brEq: ConstT BrFunc := WO~0~0~0.
    Definition brNeq: ConstT BrFunc := WO~0~0~1.
    Definition brLt: ConstT BrFunc := WO~0~1~0.
    Definition brLtu: ConstT BrFunc := WO~0~1~1.
    Definition brGe: ConstT BrFunc := WO~1~0~0.
    Definition brGeu: ConstT BrFunc := WO~1~0~1.
    Definition brAT: ConstT BrFunc := WO~1~1~0.
    Definition brNT: ConstT BrFunc := WO~1~1~1.

    Definition decodedInst :=
      STRUCT { "iType" :: IType;
               "aluFunc" :: AluFunc;
               "brFunc" :: BrFunc;
               "dst" :: Bit rfIdx; "hasDst" :: Bool;
               "src1" :: Bit rfIdx; "hasSrc1" :: Bool;
               "src2" :: Bit rfIdx; "hasSrc2" :: Bool;
               (* "csr" :: Bit csrIdx; "hasCsr" :: Bool; *)
               "imm" :: Data dataBytes; "hasImm" :: Bool
             }.

    Definition DecodedInst := Struct decodedInst.

    Definition DecodeT := forall {ty}, fullType ty (SyntaxKind (Data dataBytes)) ->
                                       Expr ty (SyntaxKind DecodedInst).

  End Decode.

  Section Execute.

    Definition execInst :=
      STRUCT { "iType" :: IType;
               "dst" :: Bit rfIdx; "hasDst" :: Bool;
               (* "csr" :: Bit csrIdx; "hasCsr" :: Bool; *)
               "data" :: Data dataBytes;
               "addr" :: Bit addrSize;
               "mispredict" :: Bool;
               "brTaken" :: Bool
             }.

    Definition ExecInst := Struct execInst.

    Definition ExecT := forall {ty}, fullType ty (SyntaxKind DecodedInst) -> (* dInst *)
                                     fullType ty (SyntaxKind (Data dataBytes)) -> (* rVal1 *)
                                     fullType ty (SyntaxKind (Data dataBytes)) -> (* rVal2 *)
                                     fullType ty (SyntaxKind (Bit addrSize)) -> (* pc *)
                                     fullType ty (SyntaxKind (Bit addrSize)) -> (* predPc *)
                                     (* fullType ty (SyntaxKind (Data dataBytes)) -> (* csrVal *) *)
                                     Expr ty (SyntaxKind ExecInst).

  End Execute.

  (* Better to define like "(UniBit (Trunc 2 _) #addr == $0", but it requires "addrSize >= 2" *)
  Definition isAligned {ty} (addr: fullType ty (SyntaxKind (Bit addrSize))) :=
    ((#addr >> $$(natToWord 2 2)) << $$(natToWord 2 2) == #addr)%kami_expr.
  
End AbstractIsa.

Hint Unfold IType iTypeUnsupported iTypeAlu iTypeLd iTypeSt
     iTypeJ iTypeJr iTypeBr iTypeCsrr iTypeCsrw iTypeAuipc
     AluFunc aluAdd aluSub aluAnd aluOr aluXor aluSlt aluSltu
     aluSll aluSra aluSrl
     BrFunc brEq brNeq brLt brLtu brGe brGeu brAT brNT
  (* decodedInst DecodedInst DecodeT *) : MethDefs.


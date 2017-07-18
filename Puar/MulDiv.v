Require Import Kami.
Require Import Lib.Indexer Lib.Struct Lib.FMap Lib.Reflection.
Require Import Kami.Tactics Kami.SemFacts.
Require Import Puar.Useful Puar.Processor FunctionalExtensionality.

Section Processor.
  Variable NumDataBytes: nat.
  Variables VAddr PAddr Inst Mode MemException ExecException: Kind.

  Variable isNotLongLat: forall ty, ty Inst -> Bool @ ty.
  
  Variable isMul: forall ty, ty Inst -> Bool @ ty.
  Variable isDiv: forall ty, ty Inst -> Bool @ ty.
  Variable isRem: forall ty, ty Inst -> Bool @ ty.

  Definition MulDivSign := Bit 2.
  Definition MulDivSignSS : ConstT MulDivSign := WO~0~0.
  Definition MulDivSignSU : ConstT MulDivSign := WO~0~1.
  Definition MulDivSignUU : ConstT MulDivSign := WO~1~0.
  Variable getMulDivSign: forall ty, ty Inst -> MulDivSign @ ty.

  Section Spec.

    Definition Data := Bit (8 * NumDataBytes).

    Definition execFnLongLatSpec ty (pc: ty VAddr)
               (inst: ty Inst) (val1 val2: ty Data)
      : (Struct (Exec NumDataBytes VAddr ExecException)) @ ty.
    Proof.
      refine (STRUCT { "data" ::= _;
                       "memVAddr" ::= $$Default;
                       "exception" ::= $$Default;
                       "nextPc" ::= $$Default })%kami_expr.
      refine (IF (isMul _ inst)
              then _
              else (IF (isDiv _ inst)
                    then _
                    else (IF (isRem _ inst)
                          then _
                          else $$Default)))%kami_expr.
      - refine (IF (getMulDivSign _ inst == $$MulDivSignSS)
                then #val1 *s #val2
                else (IF (getMulDivSign _ inst == $$MulDivSignSU)
                      then #val1 *su #val2
                      else #val1 * #val2))%kami_expr.
      - refine (IF (getMulDivSign _ inst == $$MulDivSignSS)
                then #val1 /s #val2
                else (IF (getMulDivSign _ inst == $$MulDivSignSU)
                      then #val1 /su #val2
                      else #val1 / #val2))%kami_expr.
      - refine (IF (getMulDivSign _ inst == $$MulDivSignSS)
                then BinBit (Rem _ SignSS) #val1 #val2
                else (IF (getMulDivSign _ inst == $$MulDivSignSU)
                      then BinBit (Rem _ SignSU) #val1 #val2
                      else BinBit (Rem _ SignUU) #val1 #val2))%kami_expr.
    Defined.

    Definition Spec :=
      getModFromSin (@LongLatency
                       NumDataBytes VAddr PAddr Inst Mode MemException ExecException
                       isNotLongLat execFnLongLatSpec).

  End Spec.

  Section Impl.

  End Impl.

End Processor.


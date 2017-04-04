Require Import Kami.

Set Implicit Arguments.

Section Exception.

  Definition ExceptionCause := Bit 4.
  Definition excInstAddrMisaligned: ConstT ExceptionCause := WO~0~0~0~0.
  Definition excInstAccessFault: ConstT ExceptionCause := WO~0~0~0~1.
  Definition excIllegalInst: ConstT ExceptionCause := WO~0~0~1~0.
  Definition excBreakpoint: ConstT ExceptionCause := WO~0~0~1~1.
  Definition excLoadAddrMisaligned: ConstT ExceptionCause := WO~0~1~0~0.
  Definition excLoadAccessFault: ConstT ExceptionCause := WO~0~1~0~1.
  Definition excStoreAddrMisaligned: ConstT ExceptionCause := WO~0~1~1~0.
  Definition excStoreAccessFault: ConstT ExceptionCause := WO~0~1~1~1.
  Definition excEnvCallU: ConstT ExceptionCause := WO~1~0~0~0.
  Definition excEnvCallS: ConstT ExceptionCause := WO~1~0~0~1.
  Definition excEnvCallH: ConstT ExceptionCause := WO~1~0~1~0.
  Definition excEnvCallM: ConstT ExceptionCause := WO~1~0~1~1.
  (* In order to get a 4-bit implementation in Bluespec, we need below *)
  Definition excIllegalException: ConstT ExceptionCause := WO~1~1~1~1.

  Definition setException := MethodSig "setException"(ExceptionCause): Void.
  Definition resetException := MethodSig "resetException"(): Void.
  Definition onException := MethodSig "onException"(): Bool.
  Definition getException := MethodSig "getException"(): ExceptionCause.

  Definition exception :=
    MODULE {
      Register "exception" : Struct (Maybe ExceptionCause) <- Default

      with Method "setException" (exc: ExceptionCause): Void :=
        Write "exception" <- STRUCT { "isValid" ::= $$true;
                                      "value" ::= #exc };
        Retv

      with Method "resetException" (exc: ExceptionCause): Void :=
        Write "exception" : Struct (Maybe ExceptionCause) <- STRUCT { "isValid" ::= $$false;
                                                                      "value" ::= $$Default };
        Retv

      with Method "onException" (): Bool :=
        Read exc <- "exception";
        Ret (#exc!(Maybe ExceptionCause)@."isValid")

      with Method "getException" (): ExceptionCause :=
        Read exc <- "exception";
        Ret (#exc!(Maybe ExceptionCause)@."value")
      }.

End Exception.

Hint Unfold ExceptionCause
     excInstAddrMisaligned excInstAccessFault excIllegalInst
     excBreakpoint excLoadAddrMisaligned excLoadAccessFault
     excStoreAddrMisaligned excStoreAccessFault
     excEnvCallU excEnvCallS excEnvCallH excEnvCallM
     excIllegalException
     setException resetException onException : MethDefs.
Hint Unfold exception : ModuleDefs.


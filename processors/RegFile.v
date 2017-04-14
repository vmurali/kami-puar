Require Import Kami.
Require Import Lib.CommonTactics Lib.Indexer.
Require Import Ex.MemTypes Ex.OneEltFifo.
Require Import AbstractIsa.

Set Implicit Arguments.

Section Processor.
  Variables dataBytes rfIdx: nat.

  Section RegFile.
    Definition rfStr := STRUCT { "idx" :: Bit rfIdx; "value" :: Data dataBytes }.

    Definition regFile :=
      MODULE {
        Register "rf" : Vector (Data dataBytes) rfIdx <- Default

        with Method "rd1" (idx: Bit rfIdx) : Data dataBytes :=
          Read rf <- "rf";
          Ret #rf@[#idx]

        with Method "rd2" (idx: Bit rfIdx) : Data dataBytes :=
          Read rf <- "rf";
          Ret #rf@[#idx]

        with Method "wr" (v: Struct rfStr) : Void :=
          Read rf <- "rf";
          Write "rf" <- #rf@[#v!rfStr@."idx" <- #v!rfStr@."value"];
          Retv
      }.
      
    Definition rfrd1 := MethodSig "rd1"(Bit rfIdx) : Data dataBytes.
    Definition rfrd2 := MethodSig "rd2"(Bit rfIdx) : Data dataBytes.
    Definition rfwr := MethodSig "wr"(Struct rfStr) : Void.

  End RegFile.

  Section Bypass.

    Definition BypassSt := Bit 3.
    Definition bypassStClean := WO~0~0~0.
    Definition bypassStStallE := WO~0~0~1.
    Definition bypassStStallM := WO~0~1~0.
    Definition bypassStBypassE := WO~0~1~1.
    Definition bypassStBypassM := WO~1~0~0.
    
    Definition BypassStr := STRUCT { "state" :: BypassSt; "value" :: Data dataBytes }.
    Definition BypassRegStr := STRUCT { "hasDst" :: Bool;
                                        "dst" :: Bit rfIdx;
                                        "isLd" :: Bool }.
    Definition BypassInsStr := STRUCT { "hasDst" :: Bool;
                                        "dst" :: Bit rfIdx;
                                        "value" :: Data dataBytes }.

    Definition bypass :=
      MODULE {
        Register "bpValuesE" : Vector (Data dataBytes) rfIdx <- Default
        with Register "bpValuesM" : Vector (Data dataBytes) rfIdx <- Default
        with Register "bpStatus" : Vector BypassSt rfIdx <- Default
          
        with Method "bpRegister"(r: Struct BypassRegStr): Void :=
          LET hasDst <- #r!BypassRegStr@."hasDst";
          LET dst <- #r!BypassRegStr@."dst";
          LET isLd <- #r!BypassRegStr@."isLd";

          If #hasDst then
            Read st <- "bpStatus";
            Write "bpStatus" <- #st@[#dst <- (IF #isLd then $$bypassStStallM
                                                       else $$bypassStStallE)];
            Retv;
          Retv

        with Method "bpRemove"(idx: Bit rfIdx): Void :=
          Read st <- "bpStatus";
          Write "bpStatus" <- #st@[#idx <- $$bypassStClean];
          Retv

        with Method "bpInsertE"(v: Struct BypassInsStr): Void :=
          LET hasDst <- #v!BypassInsStr@."hasDst";
          LET dst <- #v!BypassInsStr@."dst";
          LET value <- #v!BypassInsStr@."value";

          If #hasDst then
            Read st <- "bpStatus";
            Write "bpStatus" <- #st@[#dst <- $$bypassStBypassE];
            Read vals <- "bpValuesE";
            Write "bpStatus" <- #vals@[#dst <- #value];
            Retv;
          Retv

        (* with Method "bpInsertM"(v: Struct rfStr): Void := *)
        (*   LET idx <- #v!rfStr@."idx"; *)
        (*   LET value <- #v!rfStr@."value"; *)
        (*   Read st <- "bpStatus"; *)
        (*   LET bst <- #st@[#idx]; *)
        (*   If #bst != $$bypassStBypassE *)
        (*   then *)
        (*     Write "bpStatus" <- #st@[#idx <- $$bypassStBypassM]; *)
        (*     Read vals <- "bpValuesM"; *)
        (*     Write "bpStatus" <- #vals@[#idx <- #value]; *)
        (*     Retv; *)
        (*   Retv *)
              
        with Method "bpSearch1"(idx: Bit rfIdx): Struct BypassStr :=
          Read st : Vector BypassSt rfIdx <- "bpStatus";
          LET bst : BypassSt <- #st@[#idx];
          If #bst == $$bypassStBypassE
          then
            Read vals : Vector (Data dataBytes) rfIdx <- "bpValuesE";
            Ret #vals@[#idx]
          else
            Read vals : Vector (Data dataBytes) rfIdx <- "bpValuesM";
            Ret #vals@[#idx]
          as val;
          LET ret : Struct BypassStr <- STRUCT { "state" ::= #bst; "value" ::= #val };
          Ret #ret
              
        with Method "bpSearch2"(idx: Bit rfIdx): Struct BypassStr :=
          Read st : Vector BypassSt rfIdx <- "bpStatus";
          LET bst : BypassSt <- #st@[#idx];
          If #bst == $$bypassStBypassE
          then
            Read vals : Vector (Data dataBytes) rfIdx <- "bpValuesE";
            Ret #vals@[#idx]
          else
            Read vals : Vector (Data dataBytes) rfIdx <- "bpValuesM";
            Ret #vals@[#idx]
          as val;
          LET ret : Struct BypassStr <- STRUCT { "state" ::= #bst; "value" ::= #val };
          Ret #ret
      }.

    Definition bpRegister := MethodSig "bpRegister"(Struct BypassRegStr) : Void.
    Definition bpRemove := MethodSig "bpRemove"(Bit rfIdx) : Void.
    Definition bpInsertE := MethodSig "bpInsertE"(Struct BypassInsStr) : Void.
    (* Definition bpInsertM := MethodSig "bpInsertM"(Struct rfStr) : Void. *)
    Definition bpSearch1 := MethodSig "bpSearch1"(Bit rfIdx) : Struct BypassStr.
    Definition bpSearch2 := MethodSig "bpSearch2"(Bit rfIdx) : Struct BypassStr.

  End Bypass.

End Processor.

Hint Unfold rfStr rfrd1 rfrd2 rfwr
     BypassSt bypassStClean bypassStStallE bypassStStallM
     bypassStBypassE bypassStBypassM BypassStr
     bpRegister bpRemove bpInsertE bpSearch1 bpSearch2 : MethDefs.
Hint Unfold regFile bypass : ModuleDefs.

Section Wf.
  Variables addrSize dataBytes rfIdx: nat.

  Lemma regFile_ModEquiv:
    ModPhoasWf (regFile dataBytes rfIdx).
  Proof. kequiv. Qed.

  Lemma bypass_ModEquiv:
    ModPhoasWf (bypass dataBytes rfIdx).
  Proof. kequiv. Qed.

  Lemma regFile_ModRegsWf:
    ModRegsWf (regFile dataBytes rfIdx).
  Proof. kvr. Qed.

  Lemma bypass_ModRegsWf:
    ModRegsWf (bypass dataBytes rfIdx).
  Proof. kvr. Qed.

End Wf.

Hint Resolve regFile_ModEquiv bypass_ModEquiv.
Hint Resolve regFile_ModRegsWf bypass_ModRegsWf.


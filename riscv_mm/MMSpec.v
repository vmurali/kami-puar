Require Import List.

Set Implicit Arguments.
Set Asymmetric Patterns.

Local Notation "a ;; b" := (a ++ b :: nil) (at level 80).

Section ProcSpec.
  Variable IAddr DAddr Data State FenceT: Set.
  Definition Mem := DAddr -> Data.
  
  Variable decDAddr: forall a1 a2: DAddr, {a1 = a2} + {a1 <> a2}.

  Inductive Inst: Set :=
  | Nm (op: State -> State)
  | Load (addr: State -> DAddr) (ret: Data -> State -> State)
  | Store (addr: State -> DAddr) (data: State -> Data) (op: State -> State)
  | RMW (addr: State -> DAddr) (ret: Data -> State -> State) (data: State -> Data -> Data) (* First read then write *)
  | Fence (f: FenceT) (op: State -> State).
  
  Variable pc: State -> IAddr.

  Inductive SpecLabel: Set :=
  | SpecMem: IAddr -> DAddr -> option Data -> option Data -> SpecLabel  (* First read then write *)
  | SpecNm: IAddr -> SpecLabel
  | SpecFence: IAddr -> FenceT -> SpecLabel.

  Section Spec.
    Variable prog: IAddr -> Inst.
    Variable initState: State.
    Variable initMem: Mem.

    Section I2E_step.
      Variable s: State.
      
      Inductive I2E_step: SpecLabel -> State -> Prop :=
      | NmExec op:
          prog (pc s) = Nm op ->
          I2E_step (SpecNm (pc s)) (op s)
      | LoadExec addr ret v:
          prog (pc s) = Load addr ret ->
          I2E_step (SpecMem (pc s) (addr s) (Some v) None) (ret v s)
      | StoreExec addr data op:
          prog (pc s) = Store addr data op ->
          I2E_step (SpecMem (pc s) (addr s) None (Some (data s))) (op s)
      | RMWExec addr data ret v:
          prog (pc s) = RMW addr ret data ->
          I2E_step (SpecMem (pc s) (addr s) (Some v) (Some (data s v))) (ret v s)
      | FenceExec f op:
          prog (pc s) = Fence f op ->
          I2E_step (SpecFence (pc s) f) (op s).

      Section Inside.
        Variable mem: Mem.
        Inductive I2E_fullstep: State -> Mem -> Prop :=
        | NmFullExec op:
            prog (pc s) = Nm op ->
            I2E_fullstep (op s) mem
        | LoadFullExec addr ret:
            prog (pc s) = Load addr ret ->
            I2E_fullstep (ret (mem (addr s)) s) mem
        | StoreFullExec addr data op:
            prog (pc s) = Store addr data op ->
            I2E_fullstep (op s) (fun a' => if decDAddr (addr s) a' then (data s) else mem a')
        | RMWFullExec addr data ret:
            prog (pc s) = RMW addr ret data ->
            I2E_fullstep (ret (mem (addr s)) s) (fun a' => if decDAddr (addr s) a' then (data s (mem (addr s))) else mem a')
        | FenceFullExec f op:
            prog (pc s) = Fence f op ->
            I2E_fullstep (op s) mem.
      End Inside.
    End I2E_step.

    Inductive I2E_execution: list SpecLabel -> State -> Prop :=
    | Init: I2E_execution nil initState
    | Step execs s nextExec nextState:
        I2E_execution execs s ->
        I2E_step s nextExec nextState ->
        I2E_execution (execs ;; nextExec) nextState.

    Inductive I2E_fullexecution: State -> Mem -> Prop :=
    | InitFull: I2E_fullexecution initState initMem
    | FullStep s mem nextState nextMem:
        I2E_fullexecution s mem ->
        I2E_fullstep s mem nextState nextMem ->
        I2E_fullexecution nextState nextMem.

    Definition exists_n_execution n :=
      exists ls finalState,
        I2E_execution ls finalState /\
        length (filter (fun e => match e with
                                   | SpecMem _ _ (Some _) _ => true
                                   | _ => false
                                 end) ls) = n.
  End Spec.

  Section ImplTrace.
    Variable prog: IAddr -> Inst.
    Variable initState: State.
    Variable load_oracle: list Data.
    Variable load_oracle_good: exists_n_execution prog initState (length load_oracle).

    Inductive LoadResult :=
    | Ld_Normal
    | Ld_StBypass
    | Ld_RMWBypass.

    Inductive RMWResult :=
    | RMW_Normal
    | RMW_StBypass (n: nat)
    | RMW_RMWBypass (n: nat).

    Inductive ImplLabel: Set :=
    | ExecLd: DAddr -> Data -> ImplLabel
    | ExecSt: DAddr -> Data -> ImplLabel
    | ExecRMW: DAddr -> Data -> Data -> ImplLabel (* First read, then write *)
    | ExecFence: FenceT -> ImplLabel
    | CommitNm: IAddr -> ImplLabel
    | CommitLd: LoadResult -> nat -> IAddr -> DAddr -> Data -> ImplLabel
    | CommitSt: nat -> IAddr -> DAddr -> Data -> ImplLabel
    | CommitRMW: RMWResult -> nat -> IAddr -> DAddr -> Data -> Data -> ImplLabel (* First read, then write *)
    | CommitFence: IAddr -> FenceT -> ImplLabel.

    Variable trace: list ImplLabel.
    Variable finalState: State.

    Local Definition NoSt_in_between init final a :=
      forall n, init < n < final ->
                forall pc n' a' d, nth_error trace n = Some (CommitSt pc n' a' d) ->
                                   a <> a'.

    Local Definition NoRMW_in_between init final a :=
      forall n, init < n < final ->
                forall res pc n' a' read write, nth_error trace n = Some (CommitRMW res pc n' a' read write) ->
                                                a <> a'.
    
    Definition NoWrite_in_between init final a :=
      NoSt_in_between init final a /\ NoRMW_in_between init final a.
    
    Inductive SpecLabel_stripped :=
    | SpecMem_stripped: DAddr -> option Data -> option Data -> SpecLabel_stripped  (* First read then write *)
    | SpecFence_stripped: FenceT -> SpecLabel_stripped.

    Local Definition removeNone A (l: list (option A)) := filter (fun x => match x with Some _ => true | None => false end) l.
    
    Local Definition stripSpecLabel l :=
      removeNone
        (map (fun x => match x with
                         | SpecMem _ a d1 d2 => Some (SpecMem_stripped a d1 d2)
                         | SpecFence _ f => Some (SpecFence_stripped f)
                         | _ => None
                       end) l).

    Local Definition stripImplLabel l :=
      removeNone
        (map (fun x => match x with
                         | CommitLd _ _ pc a d => Some (SpecMem_stripped a (Some d) None)
                         | CommitSt _ pc a d => Some (SpecMem_stripped a None (Some d))
                         | CommitRMW _ _ pc a read write => Some (SpecMem_stripped a (Some read) (Some write))
                         | CommitFence pc f => Some (SpecFence_stripped f)
                         | _ => None
                       end) l).

    Record SameAddr_ordering :=
      { ImplTrace_load_store_exec_order:
          forall i j ei pc a d ej pc' d',
            nth_error trace i = Some (CommitLd Ld_Normal ei pc a d) ->
            nth_error trace j = Some (CommitSt ej pc' a d') ->
            PeanoNat.Nat.compare i j = PeanoNat.Nat.compare ei ej;
        
        ImplTrace_load_rmw_exec_order:
          forall i j ei pc a d res ej pc' read write,
            nth_error trace i = Some (CommitLd Ld_Normal ei pc a d) ->
            nth_error trace j = Some (CommitRMW res ej pc' a read write) ->
            PeanoNat.Nat.compare i j = PeanoNat.Nat.compare ei ej;        

        ImplTrace_store_store_exec_order:
          forall i j ei pc a d ej pc' d',
            nth_error trace i = Some (CommitSt ej pc a d) ->
            nth_error trace j = Some (CommitSt ej pc' a d') ->
            PeanoNat.Nat.compare i j = PeanoNat.Nat.compare ei ej;

        ImplTrace_store_rmw_exec_order:
          forall i j ei pc a d res ej pc' read write,
            nth_error trace i = Some (CommitSt ei pc a d) ->
            nth_error trace j = Some (CommitRMW res ej pc' a read write) ->
            PeanoNat.Nat.compare i j = PeanoNat.Nat.compare ei ej;        

        ImplTrace_rmw_rmw_exec_order:
          forall i j res ei pc a read write res' ej pc' read' write',
            nth_error trace i = Some (CommitRMW res ei pc a read write) ->
            nth_error trace j = Some (CommitRMW res' ej pc' a read' write') ->
            PeanoNat.Nat.compare i j = PeanoNat.Nat.compare ei ej
      }.

    
    Record ImplTrace_correct :=
      { Match_Ld_Normal: forall commitPos pc execPos a d,
                           nth_error trace commitPos = Some (CommitLd Ld_Normal execPos pc a d) ->
                           execPos < commitPos /\
                           nth_error trace execPos = Some (ExecLd a d);
        Match_Ld_StBypass: forall commitPos pc stCommitPos a d,
                             nth_error trace commitPos = Some (CommitLd Ld_StBypass stCommitPos pc a d) ->
                             stCommitPos < commitPos /\
                             NoWrite_in_between stCommitPos commitPos a /\
                             exists n pc', nth_error trace stCommitPos = Some (CommitSt n pc' a d);
        Match_Ld_RMWBypass: forall commitPos pc rmwCommitPos a d,
                              nth_error trace commitPos = Some (CommitLd Ld_RMWBypass rmwCommitPos pc a d) ->
                              rmwCommitPos < commitPos /\
                              NoWrite_in_between rmwCommitPos commitPos a /\
                              exists res n pc' w, nth_error trace rmwCommitPos = Some (CommitRMW res n pc' a d w);
        Match_St: forall commitPos pc execPos a d,
                    nth_error trace commitPos = Some (CommitSt execPos pc a d) ->
                    execPos < commitPos /\
                    nth_error trace execPos = Some (ExecSt a d);
        Match_RMW_Normal: forall commitPos pc execPos a read write,
                            nth_error trace commitPos = Some (CommitRMW RMW_Normal execPos pc a read write) ->
                            execPos < commitPos /\
                            nth_error trace execPos = Some (ExecRMW a read write);
        Match_RMW_StBypass: forall commitPos pc execPos stCommitPos a read write,
                              nth_error trace commitPos = Some (CommitRMW (RMW_StBypass stCommitPos) execPos pc a read write) ->
                              execPos < commitPos /\
                              nth_error trace execPos = Some (ExecRMW a read write) /\
                              stCommitPos < commitPos /\
                              NoWrite_in_between stCommitPos commitPos a /\
                              exists n pc', nth_error trace stCommitPos = Some (CommitSt n pc' a read);
        Match_RMW_RMWBypass: forall commitPos pc execPos rmwCommitPos a read write,
                               nth_error trace commitPos = Some (CommitRMW (RMW_RMWBypass rmwCommitPos) execPos pc a read write) ->
                               execPos < commitPos /\
                               nth_error trace execPos = Some (ExecRMW a read write) /\
                               rmwCommitPos < commitPos /\
                               NoWrite_in_between rmwCommitPos commitPos a /\
                               exists res n pc' r, nth_error trace rmwCommitPos = Some (CommitRMW res n pc' a r read);
        
        LoadResult_matches_oracle: forall i,
                                     match nth_error (filter (fun e => match e with
                                                                         | ExecLd _ _ => true
                                                                         | ExecRMW _ _ _ => true
                                                                         | _ => false
                                                                       end) trace) i with
                                       | Some (ExecLd a d) => d = load_oracle i
                                       | Some (ExecRMW a read write) => read = load_oracle i
                                       | _ => True
                                     end;
        
        ImplTrace_matches_spec: exists specTrace,
                                  I2E_execution prog initState specTrace finalState /\
                                  stripSpecLabel specTrace = stripImplLabel trace;
        
        SameAddr_required_ordering: SameAddr_ordering
      }.
  End ImplTrace.

  Variable impl: (IAddr -> Inst) -> State -> (nat -> Data) -> list ImplLabel -> State -> Prop.

  Definition Impl_is_correct :=
    forall prog initState load_oracle,
      (exists implTrace finalState, impl prog initState load_oracle implTrace finalState) /\
      forall implTrace finalState,
        impl prog initState load_oracle implTrace finalState ->
        ImplTrace_correct load_oracle prog initState implTrace finalState.

  Section Uniprocessor.
    Variable prog: IAddr -> Inst.
    Variable initState: State.

    Section Inside.
      Variable s: State.
      Variable mem: Mem.
      Inductive I2E_fullstep: State -> Mem -> Prop :=
      | NmFullExec op:
          prog (pc s) = Nm op ->
          I2E_fullstep (op s) mem
      | LoadFullExec addr ret:
          prog (pc s) = Load addr ret ->
          I2E_fullstep (ret (mem (addr s)) s) mem
      | StoreFullExec addr data op:
          prog (pc s) = Store addr data op ->
          I2E_fullstep (op s) (fun a' => if decDAddr (addr s) a' then (data s) else mem a')
      | RMWFullExec addr data ret:
          prog (pc s) = RMW addr ret data ->
          I2E_fullstep (ret (mem (addr s)) s) (fun a' => if decDAddr (addr s) a' then (data s (mem (addr s))) else mem a')
      | FenceFullExec f op:
          prog (pc s) = Fence f op ->
          I2E_fullstep (op s) mem.

      Inductive ImplTrace_matches_memory : Mem -> list ImplLabel -> Prop :=
      | EmptyImplTrace: ImplTrace_matches_memory mem nil
      | LdImplLabel a trace:
          ImplTrace_matches_memory mem trace ->
          ImplTrace_matches_memory mem (trace ;; ExecLd a (mem a))
      | StImplLabel a d trace:
          ImplTrace_matches_memory mem trace ->
          ImplTrace_matches_memory (fun a' => if decDAddr a a' then d else mem a) (trace ;; ExecSt a d)
      | RMWImplLabel a read write trace:
          ImplTrace_matches_memory mem trace ->
          ImplTrace_matches_memory (fun a' => if decDAddr a a' then write else mem a) (trace ;; ExecRMW a read write)
      | FenceImplLabel f trace:
          ImplTrace_matches_memory mem trace ->
          ImplTrace_matches_memory mem (trace ;; ExecFence f).
    End Inside.

  End Uniprocessor.

  Theorem uniprocessor_mem_state_same:
    Impl_is_correct ->
    forall prog initState load_oracle initMem finalState finalMem implTrace,
      impl prog initState load_oracle implTrace finalState ->
      ImplTrace_matches_memory initMem finalMem implTrace ->
      I2E_fullexecution prog initState initMem finalState finalMem.
  Proof.
    admit.
  Admitted.
End ProcSpec.


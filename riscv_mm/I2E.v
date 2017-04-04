Require Import List.

Section I2E.
  Variable Addr Data State FenceT: Set.

  Inductive Inst: Set :=
  | Nm (op: State -> State)
  | Load (addr: State -> Addr) (ret: Data -> State -> State)
  | Store (addr: State -> Addr) (data: State -> Data) (op: State -> State)
  | RMW (addr: State -> Addr) (data: State -> Data) (ret: Data -> State -> State)
  | Fence (f: FenceT) (op: State -> State).
  
  Variable prog: Addr -> Inst.
  Variable pc: State -> Addr.

  Inductive Event: Set :=
  | EventLoad: Addr -> Data -> Event
  | EventStore: Addr -> Data -> Event
  | EventRMW: Addr -> Data -> Data -> Event
  | EventFence: FenceT -> Event.

  Section ProcI2E_step.
    Variable s: State.
    Inductive ProcI2E_step: option Event -> State -> Prop :=
    | NmExec op:
        prog (pc s) = Nm op ->
        ProcI2E_step None (op s)
    | LoadExec addr ret v:
        prog (pc s) = Load addr ret ->
        ProcI2E_step (Some (EventLoad (addr s) v)) (ret v s)
    | StoreExec addr data op:
        prog (pc s) = Store addr data op ->
        ProcI2E_step (Some (EventStore (addr s) (data s))) (op s)
    | RMWExec addr data ret v:
        prog (pc s) = RMW addr data ret ->
        ProcI2E_step (Some (EventRMW (addr s) (data s) v)) (ret v s)
    | FenceExec f op:
        prog (pc s) = Fence f op ->
        ProcI2E_step (Some (EventFence f)) (op s).
  End ProcI2E_step.

  Variable initState: State.

  Inductive ProcI2E_execution: list Event -> State -> Prop :=
  | Init: ProcI2E_execution nil initState
  | Step events s nextEvent nextState:
      ProcI2E_execution events s ->
      ProcI2E_step s nextEvent nextState ->
      ProcI2E_execution match nextEvent with
                          | None => events
                          | Some e => e :: events
                        end nextState.

  Section ImplTrace.
    Variable loadResult: Addr -> nat -> Data.

    Inductive ImplEvent: Set :=
    | ExecEvent: Event -> ImplEvent
    | CommitLoadMem: nat -> ImplEvent
    | CommitLoadStoreBypass: nat -> ImplEvent
    | CommitLoadRMWBypass: nat -> ImplEvent
    | CommitStore: nat -> ImplEvent
    | CommitRMW: nat -> ImplEvent
    | CommitFence: nat -> ImplEvent.

    Definition ImplEvents := list ImplEvent.

    Definition ImplEvents_well_formed ls :=
      forall pos e,
        nth_error ls pos = Some e ->
        match e with
          | ExecEvent e => True
          | CommitLoadMem n => n <= pos /\ exists a d, nth_error ls n = Some (ExecEvent (EventLoad a d))
          | CommitLoadStoreBypass n => n < pos /\ exists n', nth_error ls n = Some (CommitStore n')
          | CommitLoadRMWBypass n => n < pos /\ exists n', nth_error ls n = Some (CommitRMW n')
          | CommitStore n => n <= pos /\ exists a d, nth_error ls n = Some (ExecEvent (EventStore a d))
          | CommitRMW n => n <= pos /\ exists a d ret, nth_error ls n = Some (ExecEvent (EventRMW a d ret))
          | CommitFence n => n <= pos /\ exists f, nth_error ls n = Some (ExecEvent (EventFence f))
        end.

    Definition ImplEvents_match_loadResult ls :=
      forall a pos,
        nth_error (filter (fun e => match e with
                                      | ExecEvent (EventLoad a d) => true
                                      | _ => false
                                    end) ls) pos = Some (ExecEvent (EventLoad a (loadResult a pos))).

    Definition ImplEvents_store_bypass_correct ls :=
      forall curr storeCommitPos storePos a d1,
        nth_error ls curr = Some (CommitLoadStoreBypass storeCommitPos) ->
        nth_error ls storeCommitPos = Some (CommitStore storePos) ->
        nth_error ls storePos = Some (ExecEvent (EventStore a d1)) ->
         forall n,
           storeCommitPos < n < curr ->
           forall n', ((nth_error ls n = Some (CommitStore n') ->
                        forall d2, nth_error ls n' <> Some (ExecEvent (EventStore a d2))) /\
                       (nth_error ls n = Some (CommitRMW n') ->
                        forall d2 ret, nth_error ls n' <> Some (ExecEvent (EventRMW a d2 ret)))).

    Definition ImplEvents_rmw_bypass_correct ls :=
      forall curr storeCommitPos storePos a d1 ret,
        nth_error ls curr = Some (CommitLoadRMWBypass storeCommitPos) ->
        nth_error ls storeCommitPos = Some (CommitRMW storePos) ->
        nth_error ls storePos = Some (ExecEvent (EventRMW a d1 ret)) ->
         forall n,
           storeCommitPos < n < curr ->
           forall n', ((nth_error ls n = Some (CommitStore n') ->
                        forall d2, nth_error ls n' <> Some (ExecEvent (EventStore a d2))) /\
                       (nth_error ls n = Some (CommitRMW n') ->
                        forall d2 ret, nth_error ls n' <> Some (ExecEvent (EventRMW a d2 ret)))).

    Variable impl: (Addr -> Inst) -> (Addr -> nat -> Data) -> ImplEvents.

    Definition implTrace := impl prog loadResult.

    Definition goodImplTrace :=
      ImplEvents_well_formed implTrace /\
      ImplEvents_match_loadResult implTrace /\
      ImplEvents_store_bypass_correct implTrace /\
      ImplEvents_rmw_bypass_correct implTrace.
  End ImplTrace.
End I2E.

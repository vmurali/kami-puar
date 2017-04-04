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

  Inductive Exec: Set :=
  | ExecLoad: Addr -> Data -> Exec
  | ExecStore: Addr -> Data -> Exec
  | ExecRMW: Addr -> Data -> Data -> Exec
  | ExecFence: FenceT -> Exec.

  Section ProcI2E_step.
    Variable s: State.
    Inductive ProcI2E_step: option Exec -> State -> Prop :=
    | NmExec op:
        prog (pc s) = Nm op ->
        ProcI2E_step None (op s)
    | LoadExec addr ret v:
        prog (pc s) = Load addr ret ->
        ProcI2E_step (Some (ExecLoad (addr s) v)) (ret v s)
    | StoreExec addr data op:
        prog (pc s) = Store addr data op ->
        ProcI2E_step (Some (ExecStore (addr s) (data s))) (op s)
    | RMWExec addr data ret v:
        prog (pc s) = RMW addr data ret ->
        ProcI2E_step (Some (ExecRMW (addr s) (data s) v)) (ret v s)
    | FenceExec f op:
        prog (pc s) = Fence f op ->
        ProcI2E_step (Some (ExecFence f)) (op s).
  End ProcI2E_step.

  Variable initState: State.

  Inductive ProcI2E_execution: list Exec -> State -> Prop :=
  | Init: ProcI2E_execution nil initState
  | Step events s nextExec nextState:
      ProcI2E_execution events s ->
      ProcI2E_step s nextExec nextState ->
      ProcI2E_execution match nextExec with
                          | None => events
                          | Some e => e :: events
                        end nextState.

  Section ImplTrace.
    Variable loadResult: Addr -> nat -> Data.

    Inductive ImplExec: Set :=
    | DoExec: Exec -> ImplExec
    | CommitLoadMem: nat -> ImplExec
    | CommitLoadStoreBypass: nat -> ImplExec
    | CommitLoadRMWBypass: nat -> ImplExec
    | CommitStore: nat -> ImplExec
    | CommitRMW: nat -> ImplExec
    | CommitFence: nat -> ImplExec.

    Definition ImplExecs := list ImplExec.

    Definition ImplExecs_well_formed ls :=
      forall pos e,
        nth_error ls pos = Some e ->
        match e with
          | DoExec e => True
          | CommitLoadMem n => n <= pos /\ exists a d, nth_error ls n = Some (DoExec (ExecLoad a d))
          | CommitLoadStoreBypass n => n < pos /\ exists n', nth_error ls n = Some (CommitStore n')
          | CommitLoadRMWBypass n => n < pos /\ exists n', nth_error ls n = Some (CommitRMW n')
          | CommitStore n => n <= pos /\ exists a d, nth_error ls n = Some (DoExec (ExecStore a d))
          | CommitRMW n => n <= pos /\ exists a d ret, nth_error ls n = Some (DoExec (ExecRMW a d ret))
          | CommitFence n => n <= pos /\ exists f, nth_error ls n = Some (DoExec (ExecFence f))
        end.

    Definition ImplExecs_match_loadResult ls :=
      forall a pos,
        nth_error (filter (fun e => match e with
                                      | DoExec (ExecLoad a d) => true
                                      | _ => false
                                    end) ls) pos = Some (DoExec (ExecLoad a (loadResult a pos))).

    Definition ImplExecs_store_bypass_correct ls :=
      forall curr storeCommitPos storePos a d1,
        nth_error ls curr = Some (CommitLoadStoreBypass storeCommitPos) ->
        nth_error ls storeCommitPos = Some (CommitStore storePos) ->
        nth_error ls storePos = Some (DoExec (ExecStore a d1)) ->
         forall n,
           storeCommitPos < n < curr ->
           forall n', ((nth_error ls n = Some (CommitStore n') ->
                        forall a2 d2, nth_error ls n' = Some (DoExec (ExecStore a2 d2)) ->
                                      a2 <> a) /\
                       (nth_error ls n = Some (CommitRMW n') ->
                        forall a2 d2 ret, nth_error ls n' <> Some (DoExec (ExecRMW a d2 ret)) ->
                                          a2 <> a)).

    Definition ImplExecs_rmw_bypass_correct ls :=
      forall curr storeCommitPos storePos a d1 ret,
        nth_error ls curr = Some (CommitLoadRMWBypass storeCommitPos) ->
        nth_error ls storeCommitPos = Some (CommitRMW storePos) ->
        nth_error ls storePos = Some (DoExec (ExecRMW a d1 ret)) ->
         forall n,
           storeCommitPos < n < curr ->
           forall n', ((nth_error ls n = Some (CommitStore n') ->
                        forall a2 d2, nth_error ls n' = Some (DoExec (ExecStore a2 d2)) ->
                                      a2 <> a) /\
                       (nth_error ls n = Some (CommitRMW n') ->
                        forall a2 d2 ret, nth_error ls n' <> Some (DoExec (ExecRMW a d2 ret)) ->
                                          a2 <> a)).

    Definition ImplExecs_syntactic_check ls :=
      ImplExecs_well_formed ls /\
      ImplExecs_match_loadResult ls /\
      ImplExecs_store_bypass_correct ls /\
      ImplExecs_rmw_bypass_correct ls.

  End ImplTrace.
End I2E.


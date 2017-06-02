Require Import List Kami.

Set Implicit Arguments.
Set Asymmetric Patterns.

Section list.
  Variable A B: Type.
  Variable f: A -> B -> A.

  Fixpoint nth_upd val n ls :=
    match ls with
    | nil => nil
    | x :: xs => match n with
                 | 0 => f x val :: xs
                 | S m => x :: nth_upd val m xs
                 end
    end.

  Lemma nth_upd_length (b: B) (l1: list A): forall a l2,
      nth_upd b (length l1) (l1 ++ a :: l2) = l1 ++ f a b :: l2.
  Proof.
    induction l1; simpl; auto; intros.
    f_equal; auto.
  Qed.

  Fixpoint updList (val: A) n ls :=
    match ls with
    | nil => nil
    | x :: xs => match n with
                 | 0 => val :: xs
                 | S m => x :: updList val m xs
                 end
    end.

  Fixpoint rmList n (ls: list A) :=
    match ls with
    | nil => nil
    | x :: xs => match n with
                 | 0 => xs
                 | S m => x :: rmList m xs
                 end
    end.

  Lemma nth_len (def: A) l1:
    forall a l2, nth (length l1) (l1 ++ a :: l2) def = a.
  Proof.
    induction l1; intros; simpl; auto.
  Qed.
    
  
  (* Fixpoint updList A (val: A) n ls:= *)
  (*   match n with *)
  (*   | 0 => match ls with *)
  (*          | x :: xs => val :: xs *)
  (*          | nil => nil *)
  (*          end *)
  (*   | S m => match ls with *)
  (*            | x :: xs => updList val m xs *)
  (*            | nil => nil *)
  (*            end *)
  (*   end. *)

  (* Fixpoint rmList A n (ls: list A) := *)
  (*   match n with *)
  (*   | 0 => match ls with *)
  (*          | x :: xs => xs *)
  (*          | nil => nil *)
  (*          end *)
  (*   | S m => match ls with *)
  (*            | x :: xs => rmList m xs *)
  (*            | nil => nil *)
  (*            end *)
  (*   end. *)

  Definition indexIn i (ls: list A) :=
    match Compare_dec.lt_dec i (length ls) with
    | left _ => ConstBool true
    | right _ => ConstBool false
    end.

  Definition notNil (ls: list A) :=
    match ls with
    | nil => ConstBool false
    | _ => ConstBool true
    end.

  Fixpoint rmNone (ls: list (option A)) :=
    match ls with
    | nil => nil
    | Some x :: xs => x :: rmNone xs
    | None :: xs => rmNone xs
    end.
  (* Fixpoint rmNone A (ls: list (option A)) := *)
  (*   match ls with *)
  (*   | nil => nil *)
  (*   | x :: xs => match x with *)
  (*                | Some y => [y] *)
  (*                | None => nil *)
  (*                end ++ rmNone xs *)
  (*   end. *)


  Fixpoint partition C n (ls: list C) :=
    match ls with
    | nil => (nil, nil)
    | x :: xs => match n with
                 | 0 => (x :: nil, xs)
                 | S m => (x :: fst (partition m xs), snd (partition m xs))
                 end
    end.
  (* Fixpoint partition B n (ls: list B) := *)
  (*   match n with *)
  (*   | 0 => match ls with *)
  (*          | nil => (nil, nil) *)
  (*          | x :: xs => (x :: nil, xs) *)
  (*          end *)
  (*   | S m => match ls with *)
  (*            | nil => (nil, nil) *)
  (*            | x :: xs => *)
  (*              (x :: fst (partition m xs), snd (partition m xs)) *)
  (*            end *)
  (*   end. *)

  Lemma rmNonePartition: forall n (ls: list (option A)),
      rmNone ls = rmNone (fst (partition n ls)) ++ rmNone (snd (partition n ls)).
  Proof.
    intros n ls.
    generalize n; clear n.
    induction ls; destruct n; simpl; auto.
    - destruct a; reflexivity.
    - destruct a; simpl; f_equal; auto.
  Qed.

  Lemma rmNoneNil: rmNone [None] = (nil: list A).
  Proof.
    reflexivity.
  Qed.
End list.

Ltac rmNoneNilLtac := rewrite ?rmNoneNil, ?app_nil_r, ?app_nil_l in *.

Notation rmSome def x := match x with
                         | Some y => y
                         | None => def
                         end.

Notation isValid x := match x with
                      | Some _ => ConstBool true
                      | None => ConstBool false
                      end.


Open Scope string.
Notation data := "data".
Notation valid := "valid".
Close Scope string.

Notation opt T :=
  (STRUCT {
       valid :: Bool;
       data :: T }).
Notation opt' := (opt _).

Notation optT T := (Struct (opt T)).

Open Scope kami_expr.
Notation none :=
  STRUCT {
      valid ::= $$ false;
      data ::= $$ Default }.

Notation some val :=
  STRUCT {
      valid ::= $$ true;
      data ::= val }.

Definition isSome ty T (v: (optT T) @ ty) := v!(opt T)@.valid.
Definition getSome ty T (v: (optT T) @ ty) := v!(opt T)@.data.

Notation "<| t |>" := (fullType type (SyntaxKind t)).

Notation "<[ t ]>" := (fullType type (@NativeKind t nil)).

Ltac metaFlatten m :=
  let y :=
      eval cbv
           [m modFromMeta metaRegs metaRules metaMeths
              Concat.concat map nameVal
              getListFromMetaReg getListFromMetaRule
              getListFromMetaMeth getActionFromSin getSinAction] in
  (modFromMeta m) in
      let z := eval cbn [app] in y in
          exact z.

Fixpoint find_def A (f: A -> bool) (def: A) (l: list A) :=
  match l with
  | nil => def
  | cons x xs => if f x
                 then x
                 else find_def f def xs
  end.

Require Import Lib.Struct.

Definition def_rule: Attribute (Action Void)
  := {| attrName := "";
        attrType := fun ty => Return $$ WO |}%kami_expr.

Arguments StringEq.string_eq !s1 !s2.

Ltac getRule m rn :=
  let y := eval simpl in
  (find_def (fun x => if string_dec (attrName x) rn then true else false)
            def_rule (getRules m))
    in exact y.

Notation ruleMapInst thetaR imp spec rule :=
  (forall oImp uImp ruleImp csImp oSpec,
      thetaR oImp oSpec ->
      ltac:(getRule imp rule) = ruleImp ->
      SemAction oImp (attrType ruleImp type) uImp csImp WO ->
      ((csImp = []%fmap /\ thetaR (M.union uImp oImp) oSpec) \/
       (exists ruleSpec,
           In ruleSpec (getRules spec) /\
           exists uSpec,
             SemAction oSpec (attrType ruleSpec type) uSpec csImp WO /\
             thetaR (M.union uImp oImp) (M.union uSpec oSpec)))).

Close Scope kami_expr.

Ltac simplInv :=
  intros; subst;
  match goal with
  | H: SemAction _ _ _ _ _ |- _ => unfold attrType at 1 in H
  end.

Lemma evalExprRewrite K (e: K@type): evalExpr (#(evalExpr e)%kami_expr) = evalExpr e.
Proof.
  induction e; simpl in *; auto.
Qed.


Definition countTrue (ls: list bool) := count_occ bool_dec ls true.

Lemma countTrueLtSize ls: (countTrue ls <= length ls)%nat.
Proof.
  induction ls; intros; unfold countTrue in *;
    simpl; try match goal with
               | |- context[match ?p with _ => _ end] =>
                 destruct p
               end; try Omega.omega.
Qed.

Lemma bool_false: forall a b, (a = b -> False) -> a = negb b.
Proof.
  intros.
  destruct a, b; auto.
  specialize (H eq_refl); contradiction.
Qed.
                            

Require Import Kami.SymEvalTac Kami.SymEval Kami.MapReifyEx.

Local Ltac simplMapUpds' t m k :=
  let mr := mapVR_Others t O m in
  rewrite <- (findMVR_find_string mr k eq_refl) in *;
  cbn [findMVR_string] in *;
  rewrite ?StringEq.string_eq_dec_false by (intro; discriminate).

Ltac simplMapUpds :=
  match goal with
  | |- context[M.find (elt := sigT ?t) ?k ?m] =>
    simplMapUpds' t m k
  | H: context[M.find (elt := sigT ?t) ?k ?m] |- _ =>
    simplMapUpds' t m k
  end.

Ltac SymEvalSimpl :=
  SymEval';
  cbv [SymSemAction semExpr or_wrap and_wrap eq_rect];
  repeat (simplMapUpds; intros);
  rewrite ?evalExprRewrite.

Ltac substFind :=
  match goal with
  | H: (?y === ?n .[?s])%fmap , H': (?v === ?n .[ ?s])%fmap |- _ =>
    rewrite H in H';
    apply invSome in H';
    apply Eqdep.EqdepTheory.inj_pair2 in H'; rewrite <- ?H' in *; clear H' v; intros
  end.

Lemma evalExprVarRewrite: forall k e, evalExpr (Var type k e) = e.
Proof.
  intros; reflexivity.
Qed.

Ltac simplInvHyp :=
  match goal with
  | H: _ ?si ?ss |- _ =>
    match type of si with
    | RegsT => match type of ss with
               | RegsT => destruct H
               end
    end
  end;
  SymEvalSimpl;
  repeat substFind;
  subst.

(* Ltac simplInvGoal := *)
(*   split; *)
(*   [repeat econstructor; try (reflexivity || eassumption)| *)
(*    rewrite ?evalExprVarRewrite; *)
(*    esplit; simplMapUpds; try (reflexivity || eassumption)]. *)

Lemma SemIfElse k1 old (p: Expr type (SyntaxKind Bool))
      (a a': ActionT type k1) (r1: type k1) k2 (cont: type k1 -> ActionT type k2)
      newRegs1 newRegs2 calls1 calls2 (r2: type k2) unewRegs ucalls:
  M.Disj newRegs1 newRegs2 ->
  M.Disj calls1 calls2 ->
  SemAction old (cont r1) newRegs2 calls2 r2 ->
  unewRegs = M.union newRegs1 newRegs2 ->
  ucalls = M.union calls1 calls2 ->
  (match evalExpr p with
   | true => SemAction old a newRegs1 calls1 r1
   | false => SemAction old a' newRegs1 calls1 r1
   end) ->
  SemAction old (IfElse p a a' cont) unewRegs ucalls r2.
Proof.
  intros.
  case_eq (evalExpr p); let X := fresh in intros X; rewrite X in *.
  - econstructor; eassumption.
  - econstructor; eassumption.
Qed.

Ltac simplInvGoal :=
  split;
  [repeat econstructor; try (reflexivity || eassumption) |
   rewrite ?evalExprVarRewrite;
   esplit; simplMapUpds; try (reflexivity || eassumption)].

(* Ltac simplInvGoal := *)
(*   split; *)
(*   [repeat match goal with *)
(*           | |- SemAction _ (If _ then _ else _ as _; _)%kami_action _ _ _ => *)
(*             eapply SemIfElse *)
(*           | |- SemAction _ _ _ _ _ => econstructor *)
(*           end; try (reflexivity || eassumption) | *)
(*    rewrite ?evalExprVarRewrite; *)
(*    esplit; simplMapUpds; try (reflexivity || eassumption)]. *)


(* Inductive Mark := mark. *)

(* Ltac simplInvGoal := *)
(*   split; *)
(*   [repeat match goal with *)
(*           | |- SemAction _ (If _ then _ else _ as _; _)%kami_action _ _ _ => *)
(*             eapply SemIfElse; try match goal with *)
(*                                   | |- if ?p then _ else _ => case_eq p; *)
(*                                                               let X := fresh in intros X *)
(*                                   end; match goal with *)
(*                                        | H: Mark |- _ => idtac *)
(*                                        | _ => pose proof mark *)
(*                                        end *)
(*           | |- SemAction _ _ _ _ _ => econstructor *)
(*           end; *)
(*    match goal with *)
(*    | H: Mark |- _ => clear H *)
(*    | _ => try (reflexivity || eassumption) *)
(*    end | *)
(*    rewrite ?evalExprVarRewrite; *)
(*    esplit; simplMapUpds; try (reflexivity || eassumption)]. *)

Ltac initInvRight m r :=
  simplInv; right;
  exists ltac:(getRule m r);
  split; [cbv [In getRules m]; auto|
          unfold attrType at 1;
          simplInvHyp;
          eexists;
          simplInvGoal].

Ltac simplBoolFalse :=
  repeat match goal with
         | H: ?a = ?b -> False |- _ =>
           match type of a with
           | ?t' =>
             let t := eval cbn in t' in
                 match t with
                 | bool =>  apply bool_false in H; cbv [negb] in H; subst
                 end
           end
         end.

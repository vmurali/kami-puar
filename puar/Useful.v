Require Import List Kami.

Set Implicit Arguments.
Set Asymmetric Patterns.

Fixpoint updList A (val: A) n ls:=
  match n with
  | 0 => match ls with
         | x :: xs => val :: xs
         | nil => nil
         end
  | S m => match ls with
           | x :: xs => updList val m xs
           | nil => nil
           end
  end.

Fixpoint rmList A n (ls: list A) :=
  match n with
  | 0 => match ls with
         | x :: xs => xs
         | nil => nil
         end
  | S m => match ls with
           | x :: xs => rmList m xs
           | nil => nil
           end
  end.

Open Scope string.
Definition data := "data".
Definition valid := "valid".
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

Ltac simplInl m :=
  let y :=
      eval cbv
           [m modFromMeta metaRegs metaRules metaMeths
              Concat.concat map app nameVal
              getListFromMetaReg getListFromMetaRule
              getListFromMetaMeth getActionFromSin getSinAction] in
  (modFromMeta m)
    in exact y.

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

Require Import Kami.SymEvalTac Kami.SymEval Kami.MapReifyEx.

Local Ltac simplMapUpds' t m k :=
  let mr := mapVR_Others t 0 m in
  rewrite <- (findMVR_find_string mr k eq_refl) in *;
  cbv [findMVR_string StringEq.string_eq StringEq.ascii_eq eqb andb] in *.

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

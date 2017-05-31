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


Section rmNone.
  Variable A: Type.

  Definition indexIn i (ls: list A) :=
    match Coq.Arith.Peano_dec.eq_nat_dec i (length ls) with
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

  Fixpoint partition B n (ls: list B) :=
    match n with
    | 0 => match ls with
           | nil => (nil, nil)
           | x :: xs => (x :: nil, xs)
           end
    | S m => match ls with
             | nil => (nil, nil)
             | x :: xs =>
               (x :: fst (partition m xs), snd (partition m xs))
             end
    end.

  Lemma rmNonePartition: forall n (ls: list (option A)),
      rmNone ls = rmNone (fst (partition n ls)) ++ rmNone (snd (partition n ls)).
  Proof.
    induction n; destruct ls; simpl; auto.
    - destruct o; reflexivity.
    - destruct o; simpl; f_equal; auto.
  Qed.
End rmNone.

(* Fixpoint rmNone A (ls: list (option A)) := *)
(*   match ls with *)
(*   | nil => nil *)
(*   | x :: xs => match x with *)
(*                | Some y => [y] *)
(*                | None => nil *)
(*                end ++ rmNone xs *)
(*   end. *)

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

Ltac simplInvGoal :=
  split;
  [repeat econstructor; try (reflexivity || eassumption)|
   rewrite ?evalExprVarRewrite;
   esplit; simplMapUpds; try (reflexivity || eassumption)].



Ltac initInvRight m r :=
  simplInv; right;
  exists ltac:(getRule m r);
  split; [cbv [In getRules m]; auto|
          unfold attrType at 1;
          simplInvHyp;
          eexists;
          simplInvGoal].

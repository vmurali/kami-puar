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

Notation option T :=
  (STRUCT {
       valid :: Bool;
       data :: T }).
Notation option' := (option _).

Notation optionT T := (Struct (option T)).

Open Scope kami_expr.
Notation none :=
  STRUCT {
      valid ::= $$ false;
      data ::= $$ Default }.

Notation some val :=
  STRUCT {
      valid ::= $$ true;
      data ::= val }.

Definition isSome ty T (v: (optionT T) @ ty) := v!(option T)@.valid.
Definition getSome ty T (v: (optionT T) @ ty) := v!(option T)@.data.

Close Scope kami_expr.


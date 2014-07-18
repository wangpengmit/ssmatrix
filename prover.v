(* (c) Copyright ? *)

(*****************************************************************************
  Syntactical expression transformer according to transformation commands such as
  rewrite, pattern and compute.

******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Import ssreflect.
Require Import String.

Inductive Expr :=
| EFreeVar : string -> Expr
(* bounded variables, expressed by De Bruijn indices *)
| EBoundVar : nat -> Expr
| EApp : Expr -> Expr -> Expr
| EAbs : Expr -> Expr
.

Inductive AtomPrp :=
| Unital : Expr -> AtomPrp
.

(* Proposition *)
Inductive Prp :=
| Imp : Prp -> Prp -> Prp
| Equal : Expr -> Expr -> Prp
| Forall : Prp -> Prp
| Atom : AtomPrp -> Prp
.

Inductive Cmd := 
| CmdRewrite : Prp -> Cmd
| CmdPattern : Cmd
| CmdComputeConst : Cmd
| CmdBeta : Cmd
.

Record Trans := MkTrans {
  cmd : Cmd;
  pos : nat               
}.

Require Import monad.
Open Scope string_scope.
Notation Error := (sum string).

Definition replace_at (expr : Expr) (pos : nat) (new : Expr) : Error Expr :=
  throwError "not implemented".

Definition replace_all (expr : Expr) (subterm : Expr) (new : Expr) : Expr.
admit.
Defined.

Definition doCompute (expr : Expr) : Error Expr :=
  throwError "not implemented".

Fixpoint get_subterm (expr : Expr) (pos : nat) : Error Expr :=
  throwError "not implemented".

Definition WriterError w := WriterT w Error.

Notation Env := (WriterError (list Prp)).

Definition doRewrite (org : Expr) (rule : Prp) : Env Expr :=
  throwError "not implemented".

Notation "f $ x" := (f x) (at level 110).

Fixpoint doTrans (expr : Expr) (trans : Trans) : Env Expr :=
  let: MkTrans cmd pos := trans in
  subterm <- lift $ get_subterm expr pos;;
  match cmd with
    | CmdRewrite rule =>
      new <- doRewrite subterm rule;;
      expr <- lift $ replace_at expr pos new;;
      ret expr
    | CmdPattern =>
      let f := replace_all expr subterm (EBoundVar 0) in
      ret (EApp f subterm)
    | CmdComputeConst => lift $
      value <- doCompute subterm;;
      expr <- replace_at expr pos value;;
      ret expr
    | _ => throwError "not implemented"
  end
.
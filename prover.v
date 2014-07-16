Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Import String.

Inductive Expr :=
| EFreeVar : string -> Expr
(* bounded variables, expressed by De Bruijn indices *)
| EBoundVar : nat -> Expr
| EApp : Expr -> Expr -> Expr
| EAbs : Expr -> Expr
.

Inductive RewriteRule :=
.

Inductive Cmd := 
| CmdRewrite : RewriteRule -> Cmd
| CmdPattern : Cmd
| CmdCompute : Cmd
.

Record Trans := {
  cmd : Cmd;
  pos : nat               
}.


(* A hand-written example of auto-generated .v file corresponding to witness1.txt *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
Require Import finfun bigop prime binomial ssralg.
Require Import perm zmodp.
Require Import matrix.
Require Import ssrint.

Import GRing.Theory.
Open Local Scope int_scope.
Open Local Scope ring_scope.

Local Notation "$ n" := (n%:Z) (at level 0, format "$ n").
Local Ltac pattern_set t := pattern t; let X := fresh "temp" in set X := (F in F t).

Section ex1.

Variable a : int.

Lemma ex1 : $2 * a + a * $4 = $6 * a.
Proof.
  rewrite [a * $4]mulrC.
  rewrite -[$2 * a + $4 * a]mulrDl.
  rewrite -[$2 + $4]/$6.
  by [].
Qed.

End ex1.

Section ex2.
 
Variable a : int.

Lemma ex2 : (a - a)^$2 + (a - a) = $0.
Proof.
  pattern_set (a - a).
  rewrite [a - a]addrN.
  red.
  rewrite -[$0^$2 + $0]/$0.
  by [].
Qed.

End ex2.

Section ex3.

Variable a : int.

Lemma ex3 : a / a = $1.
Proof.
  rewrite [a / a]divrr.
  by [].
Qed.

End ex3.
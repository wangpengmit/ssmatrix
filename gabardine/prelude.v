Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Export ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
Require Export finfun bigop prime binomial ssralg.
Require Export perm zmodp.
Require Export matrix.
Require Export ssrint.

Export GRing.Theory.

Module Exports.

Open Scope int_scope.
Open Scope ring_scope.

Notation "$ n" := (n%:Z) (at level 0, format "$ n").
Ltac pattern_set t := pattern t; let X := fresh "temp" in set X := (F in F t).

End Exports.

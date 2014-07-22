Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import prelude.
Import prelude.Exports.

Section ex1.

Variables a : int.

Lemma ex1 : (($2 * a) + (a * $4)) = ($6 * a).
Proof.
  rewrite [(a * $4)]mulrC.
  rewrite -[(($2 * a) + ($4 * a))]mulrDl.
  rewrite -[($2 + $4)]/$6.
  by [].
Qed.

End ex1.

Section ex2.

Variables a : int.

Lemma ex2 : (((a - a) ^ $2) + (a - a)) = $0.
Proof.
  pattern_set (a - a).
  rewrite [(a - a)]addrN.
  red.
  rewrite -[(($0 ^ $2) + $0)]/$0.
  by [].
Qed.

End ex2.

Section ex3.

Variables a : int.

Lemma ex3 : (a / a) = $1.
Proof.
  rewrite [(a / a)]divrr.
  by [].
Qed.

End ex3.



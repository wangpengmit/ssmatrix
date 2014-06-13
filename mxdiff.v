(*=============================================================*)
(* Matrix Differentiation *)
Require Import matrix.

Module MxDiff.

(* Element type *)
Variable E : diffRingType.

Definition der_matrix m n (A : 'M[E]_(m, n)) := map_mx \d A.

Notation "\dm" := (@der_matrix _ _).

Section AnyMatrix.

Variable m n r : nat.
Implicit Types A : 'M[E]_(m, n).
Implicit Types B : 'M[E]_(n, r).

Lemma Dm_product : forall A B, \dm (A *m B) = \dm A *m B + A *m \dm B.
Proof.
  admit.
Qed.

End AnyMatrix.

Section SquareMatrix.

(* Non-trival square matrices are differential unit rings *)

Variable n' : nat.
Local Notation n := n'.+1.

Definition matrix_unitDiffRingType := ?
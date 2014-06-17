(*=============================================================*)
(* Matrix Differentiation *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice fintype.
Require Import finfun bigop prime binomial.

Require Import diffalg.
Require Import matrix.
Import DiffRing.Exports.
Import UnitDiffRing.Exports.
Import ComUnitDiffRing.Exports.
Require Import ssralg.
Import GRing.
Import Zmodule.Exports.
Import Ring.Exports.
Import UnitRing.Exports.
Import Lmodule.Exports.
Import Field.Exports.
Import Lalgebra.Exports.
Import Algebra.Exports.
Import Linear.Exports.
Open Scope ring_scope.
Open Scope diff_scope.

Module Exports.

Definition der_matrix (E : diffRingType) m n (A : 'M[E]_(m, n)) := map_mx \d A.

Notation "\dm" := (@der_matrix _ _ _).

Section AnyMatrix.

(* Element type *)
Variable E : diffRingType.

Variable m n r : nat.
Implicit Types A : 'M[E]_(m, n).
Implicit Types B : 'M[E]_(n, r).

Lemma dmB A1 A2 : \dm (A1 - A2) = \dm A1 - \dm A2.
Proof.
  apply/matrixP => i k.
  by rewrite !mxE raddfB.
Qed.

Lemma dm_additive : additive (@der_matrix E m n).
Proof.
  case => ? ?.
  apply dmB.
Qed.

Lemma dmM A B : \dm (A *m B) = \dm A *m B + A *m \dm B.
Proof.
  apply/matrixP => i k.
  rewrite !mxE !raddf_sum -big_split.
  apply eq_bigr => j.
  unfold der_additive; simpl.
  by rewrite !mxE derM.
Qed.

End AnyMatrix.

Section SquareMatrix.

(* Non-trival square matrices are differential rings *)

(* Element type *)
Variable E : diffRingType.

Variable n' : nat.
Local Notation n := n'.+1.

Definition matrix_diffRingMixin := DiffRing.Mixin (@dm_additive E n n) (@dmM E n n n).
Canonical matrix_diffRingType := Eval hnf in DiffRingType 'M[E]_n matrix_diffRingMixin.

End SquareMatrix.

Section UnitSquareMatrix.

(* Non-trival square matrices with comUnitDiffRing elements are differential unit rings *)

(* Element type *)
Variable E : comUnitDiffRingType.

Variable n' : nat.
Local Notation n := n'.+1.

Canonical matrix_unitDiffRingType := Eval hnf in [unitDiffRingType of 'M[E]_n].

End UnitSquareMatrix.

End Exports.
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
Import GRing.Theory.
Open Local Scope ring_scope.
Open Local Scope diff_scope.

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

Canonical matrix_unitDiffRing := Eval hnf in [unitDiffRingType of 'M[E]_n].

End UnitSquareMatrix.

Import DiffAlgebra.Exports.

(* Matrices whose elements are algebras form another Lmodule structure whose scalars are from the underlying ring R, other than the Lmodule structure registered by matrix.matrix_lmodType whose scalars are of the same type as the matrix elements *)
Section Alg_Lmodule.

(* Scalar (constant) type *)
Variable R : ringType.

(* Element type *)
Variable E : diffAlgType R.

Variables m n : nat.
Implicit Types A B : 'M[E]_(m, n).
Implicit Types c : R.

Fact constscalemx_key : unit. Proof. by []. Qed.
Definition constscalemx c A := \matrix[constscalemx_key]_(i, j) (c *: A i j).

Local Notation "x *m: A" := (constscalemx x A) (at level 40) : ring_scope.

Lemma constscale1mx A : 1 *m: A = A.
Proof. 
  by apply/matrixP=> i j; rewrite !mxE scale1r. 
Qed.

Lemma constscalemxDl A x y : (x + y) *m: A = x *m: A + y *m: A.
Proof. by apply/matrixP=> i j; rewrite !mxE scalerDl. Qed.

Lemma constscalemxDr x A B : x *m: (A + B) = x *m: A + x *m: B.
Proof. by apply/matrixP=> i j; rewrite !mxE scalerDr. Qed.

Lemma constscalemxA x y A : x *m: (y *m: A) = (x * y) *m: A.
Proof. by apply/matrixP=> i j; rewrite !mxE scalerA. Qed.

Definition matrix_alg_lmodMixin := 
  LmodMixin constscalemxA constscale1mx constscalemxDr constscalemxDl.

Definition matrix_alg_lmodType :=
  Eval hnf in LmodType R 'M[E]_(m, n) matrix_alg_lmodMixin.

End Alg_Lmodule.

Section AlgMatrix.

(* Scalar type *)
Variable R : ringType.

(* Element type *)
Variable E : diffAlgType R.

Variable m n r : nat.
Implicit Types A : 'M[E]_(m, n).
Implicit Types B : 'M[E]_(n, r).
Implicit Types a : R.

(* Definition lift_const a := a%:A : E. *)
(* Coercion lift_const : GRing.Ring.sort >-> DiffAlgebra.sort. *)

(* Canonical matrix_alg_lmodType. *)

Lemma dm_scale a A : \dm (a *: 1 *: A) = a %:A *: \dm A.
  admit.
Qed.

End AlgMatrix.

End Exports.
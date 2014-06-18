(*=============================================================*)
(* Matrix Differentiation *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice fintype.
Require Import finfun bigop prime binomial.

Require Import diffalg.
Require Import matrix.
Require Import ssralg.
Import GRing.Theory.
Open Local Scope ring_scope.
Open Local Scope diff_scope.

Import DiffRing.Exports.
Import UnitDiffRing.Exports.
Import ComUnitDiffRing.Exports.

Definition der_mx (E : diffRingType) m n (A : 'M[E]_(m, n)) := map_mx \d A.

Notation "\dm" := (@der_mx _ _ _).

Section AnyMatrix.

(* Element type *)
Variable E : diffRingType.

Variable m n r : nat.
Implicit Types A : 'M[E]_(m, n).
Implicit Types B : 'M[E]_(n, r).

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

Import Derivative.Exports.
Canonical dm_derivative := Derivative (@dmM E n n n).

Definition matrix_diffRingMixin := DiffRingMixin (@dmM E n n n).
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

Section const_scale.

Variable R : ringType.
Variable E : diffAlgType R.
Implicit Types c : R.
Variables m n r : nat.
Implicit Types A : 'M[E]_(m, n).
Implicit Types B : 'M[E]_(n, r).
Implicit Types C : 'M[R]_(m, n).

Definition const c : E := c%:A.

Definition constm C := map_mx const C.

Definition const_scale c A : 'M[E]_(m,n) := const c *: A.

Definition const_mulmx C B : 'M[E]_(m,r) := constm C *m B.

End const_scale.

Notation "c *:: A" := (const_scale c A) (at level 40).
Notation "C *m: A" := (const_mulmx C A) (at level 40).
Notation "\const" := (@const _ _).
Notation "\constm" := (@constm _ _).
Notation "c %:C" := (@const _ _ c) (at level 8).
Notation "C %:CM" := (@constm _ _ C) (at level 8).

(* Matrices whose elements are algebras form another Lmodule structure whose scalars are from the underlying ring R, other than the Lmodule structure registered by matrix.matrix_lmodType whose scalars are of the same type as the matrix elements *)
Section Alg_Lmodule.

(* Scalar (constant) type *)
Variable R : ringType.

(* Element type *)
Variable E : diffAlgType R.

Variables m n : nat.
Implicit Types A B : 'M[E]_(m, n).
Implicit Types c : R.

(* Fact constscalemx_key : unit. Proof. by []. Qed. *)
(* Definition constscalemx c A := \matrix[constscalemx_key]_(i, j) (c *: A i j). *)
(* Local Notation "x *m: A" := (constscalemx x A) (at level 40) : ring_scope. *)

Lemma constscale1mx A : 1 *:: A = A.
Proof. 
  unfold const_scale, const.
  by rewrite !scale1r.
Qed.

Lemma constscalemxDl A x y : (x + y) *:: A = x *:: A + y *:: A.
Proof. 
  unfold const_scale, const.
  by rewrite !scalerDl.
Qed.

Lemma constscalemxDr x A B : x *:: (A + B) = x *:: A + x *:: B.
Proof. 
  unfold const_scale, const.
  by rewrite !scalerDr.
Qed.

Lemma constscalemxA x y A : x *:: (y *:: A) = (x * y) *:: A.
Proof. 
  unfold const_scale, const.
  by rewrite scalerA -scalerAl mul1r scalerA.
Qed.

Definition matrix_alg_lmodMixin := 
  LmodMixin constscalemxA constscale1mx constscalemxDr constscalemxDl.

Definition matrix_alg_lmodType :=
  Eval hnf in LmodType R 'M[E]_(m, n) matrix_alg_lmodMixin.
(* Canonical matrix_alg_lmodType. *)

End Alg_Lmodule.

Section AlgMatrix.

(* Scalar type *)
Variable R : ringType.

(* Element type *)
Variable E : diffAlgType R.

Implicit Types c : R.

Variables m n : nat.
Implicit Types A B : 'M[E]_(m, n).
Implicit Types C : 'M[R]_(m, n).

Lemma dm_scale1 c A : \dm (c *: 1 *: A) = c *: 1 *: \dm A.
Proof.
  by apply/matrixP=> i j; rewrite !mxE -scalerAl linearZ -scalerAl !mul1r.
Qed.

Lemma dm_scale_const c A : \dm (c *:: A) = c *:: \dm A.
Proof.
  by apply dm_scale1.
Qed.

Lemma dm_is_scalable : scalable (@der_mx E m n : matrix_alg_lmodType _ _ _ -> matrix_alg_lmodType _ _ _).
Proof.
  move => a A.
  by rewrite dm_scale_const.
Qed.

Lemma dm_scale c A : \dm (\const c *: A) = \const c *: \dm A.
Proof.
  by apply dm_scale1.
Qed.

Canonical dm_linear_const := AddLinear dm_is_scalable.

End AlgMatrix.

Section Paper.

(* Scalar type *)
Variable R : ringType.
(* Element type *)
Variable E : diffAlgType R.

Implicit Types c : R.
Variable m n : nat.

Lemma dm_scaleI c : \dm (c *:: 1%:M) = c *:: \dm 1%:M :> 'M[E]_n.
Proof.
  rewrite linearZ.
  by done.
Qed.
(*=============================================================*)
(* Matrix Differentiation *)
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice fintype.
Require Import finfun bigop prime binomial.

Require Import matrix.
Require Import ssralg.
Import GRing.Theory.
Open Local Scope ring_scope.

(* Generalized scalemx
   Matrices whose elements are algebras form another Lmodule structure whose scalars are from the underlying ring R, other than the Lmodule structure registered by matrix.matrix_lmodType whose scalars are of the same type as the matrix elements *)
Section gscalemx.

Variable R : ringType.
Variable E : lmodType R.
Variables m n : nat.
Implicit Types A B : 'M[E]_(m, n).
Implicit Types c : R.

Fact gscalemx_key : unit. Proof. by []. Qed.
Definition gscalemx c A := \matrix[gscalemx_key]_(i, j) (c *: A i j).
Local Notation "x *m: A" := (gscalemx x A) (at level 40) : ring_scope.

Lemma gscale1mx A : 1 *m: A = A.
Proof. by apply/matrixP=> i j; rewrite !mxE scale1r. Qed.

Lemma gscalemxDl A x y : (x + y) *m: A = x *m: A + y *m: A.
Proof. by apply/matrixP=> i j; rewrite !mxE scalerDl. Qed.

Lemma gscalemxDr x A B : x *m: (A + B) = x *m: A + x *m: B.
Proof. by apply/matrixP=> i j; rewrite !mxE scalerDr. Qed.

Lemma gscalemxA x y A : x *m: (y *m: A) = (x * y) *m: A.
Proof. by apply/matrixP=> i j; rewrite !mxE scalerA. Qed.

Definition gscalemx_lmodMixin := 
  LmodMixin gscalemxA gscale1mx gscalemxDr gscalemxDl.

Definition gscalemx_lmodType :=
  Eval hnf in LmodType R 'M[E]_(m, n) gscalemx_lmodMixin.
Canonical gscalemx_lmodType.

End gscalemx.

(* If we can register canonical structure gscalemx_lmodType, we can use the *: notation for gscalemx. But since gscalemx_lmodType overlaps with matrix_lmodType which Coq doesn't allow, here we give gscalemx_lmodType another notation *)
Notation "c *:: A" := (gscalemx c A) (at level 40).

(* A fix of scalerAr. It doesn't need a commutative ring *)
Section AlgebraTheory.

Variables (R : ringType) (A : algType R).
Implicit Types (k : R) (x y : A).

Lemma scalerAr_fix k x y : k *: (x * y) = x * (k *: y).
Proof. by case: A k x y => T []. Qed.

End AlgebraTheory.

(* On algebra-element matrices, gscalemx enjoys right-associativity *)
Section gscalemx_alg.

Variable R : ringType.
Variable E : algType R.
Variables m n r : nat.
Implicit Types A : 'M[E]_(m, n).
Implicit Types B : 'M[E]_(n, r).
Implicit Types c : R.

Lemma gscalemxAr c A B : c *:: (A *m B) = A *m (c *:: B).
Proof. 
  by apply/matrixP=> i j; rewrite !mxE !raddf_sum; apply eq_bigr => k; rewrite /= !mxE scalerAr_fix.
Qed.

End gscalemx_alg.

(* Lift a constant scalar or matrix to the correspondent L-algebra scalar or matrix *)
Section lift.

Variable R : ringType.
Variable E : lalgType R.
Implicit Types c : R.
Variables m n : nat.
Implicit Types C : 'M[R]_(m, n).
Implicit Types A : 'M[E]_(m, n).

Definition lift c : E := c%:A.

Definition liftm C := map_mx lift C.

Lemma lift_scalemx_gscalemx c A : lift c *: A = c *:: A.
Proof. by apply/matrixP=> i j; rewrite !mxE -scalerAl mul1r. Qed.

End lift.

Notation "\lift" := (@lift _ _).
Notation "\liftm" := (@liftm _ _).
Notation "C %:AM" := (@liftm _ _ C) (at level 8).

(* Parametricity over the linear structure. *)
Section MapLinear.

Variable R : ringType.
Variable E F : lmodType R.
Implicit Types c : R.
Variables m n : nat.
Implicit Types A : 'M[E]_(m, n).
Implicit Types C : 'M[R]_(m, n).
Variable f : {linear E -> F}.
Local Notation "A ^f" := (map_mx f A) : ring_scope.

Lemma fAgscalemx c A : (c *:: A)^f = c *:: A^f.
Proof. by apply/matrixP=> i j; rewrite !mxE linearZ. Qed.

Lemma f_is_scalable : scalable (@map_mx E F f m n : gscalemx_lmodType _ _ _ -> gscalemx_lmodType _ _ _).
Proof. by move => a A; rewrite fAgscalemx. Qed.

Canonical f_linear := AddLinear f_is_scalable.

End MapLinear.

Section MapLinearAlg.

Variable R : ringType.
Variable E F : lalgType R.
Implicit Types c : R.
Variables m n : nat.
Implicit Types A : 'M[E]_(m, n).
Variable f : {linear E -> F}.
Local Notation "A ^f" := (map_mx f A) : ring_scope.

Lemma fAscalemx1 c A : (c *: 1 *: A)^f = c *: 1 *: A^f.
Proof. by rewrite !lift_scalemx_gscalemx fAgscalemx. Qed.

Lemma fAlift c A : (\lift c *: A)^f = \lift c *: A^f.
Proof. by apply fAscalemx1. Qed.

End MapLinearAlg.

Require Import diffalg.
Import DiffRing.Exports.
Import UnitDiffRing.Exports.
Import ComUnitDiffRing.Exports.
Open Local Scope diff_scope.

Notation "\dm" := (map_mx \d).

Section AnyMatrix.

(* Element type *)
Variable E : diffRingType.

Variable m n r : nat.
Implicit Types A : 'M[E]_(m, n).
Implicit Types B : 'M[E]_(n, r).

Lemma dmM A B : \dm (A *m B) = \dm A *m B + A *m \dm B.
Proof.
  by apply/matrixP => i k; rewrite !mxE !raddf_sum -big_split; apply eq_bigr => j; rewrite /= !mxE derM.
Qed.

End AnyMatrix.

Section SquareMatrix.

Variable E : diffRingType.

Variable n' : nat.
Local Notation n := n'.+1.

Import Derivative.Exports.
Canonical dm_derivative := Derivative (@dmM E n n n).

Definition matrix_diffRingMixin := DiffRingMixin (@dmM E n n n).
Canonical matrix_diffRingType := Eval hnf in DiffRingType 'M[E]_n matrix_diffRingMixin.

End SquareMatrix.

Section UnitSquareMatrix.

Variable E : comUnitDiffRingType.

Variable n' : nat.
Local Notation n := n'.+1.

Canonical matrix_unitDiffRing := Eval hnf in [unitDiffRingType of 'M[E]_n].

End UnitSquareMatrix.

Import DiffAlgebra.Exports.

Section Paper.

(* Scalar type *)
Variable R : ringType.
(* Element type *)
Variable E : diffAlgType R.

Implicit Types c : R.
Variable m n : nat.
Implicit Types A : 'M[E]_(m, n).

Lemma dmAgscalemx c A : \dm (c *:: A) = c *:: \dm A.
Proof. by rewrite linearZ. Qed.

End Paper.
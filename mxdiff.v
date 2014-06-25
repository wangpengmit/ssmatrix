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

Require Import diffalg.
Import DiffRing.Exports.
Import UnitDiffRing.Exports.
Import ComUnitDiffRing.Exports.
Open Local Scope diff_scope.

Local Notation "\\d" := (map_mx \d) : diff_scope.

Section AnyMatrix.

(* Element type *)
Variable E : diffRingType.

Variable m n r : nat.
Implicit Types A : 'M[E]_(m, n).
Implicit Types B : 'M[E]_(n, r).

Lemma dmM A B : \\d (A *m B) = \\d A *m B + A *m \\d B.
Proof.
  by apply/matrixP => i k; rewrite !mxE !raddf_sum -big_split; apply eq_bigr => j; rewrite /= !mxE derM.
Qed.

End AnyMatrix.

Local Notation I := (1%:M).

Lemma dmI {E : diffRingType} {n} : \\d I = 0 :> 'M[E]_n.
Proof.
  apply: (addIr (\\d (I *m I))).
  rewrite add0r {1}mul1mx.
    by rewrite dmM mulmx1 mul1mx.
Qed.

Section SquareMatrix.

Variable E : diffRingType.

Variable n' : nat.
Local Notation n := n'.+1.

Import Derivative.Exports.
Canonical dm_derivative := Derivative (@dmM E n n n).

Definition matrix_diffRingMixin := DiffRingMixin (@dmM E n n n).
Canonical matrix_diffRingType := Eval hnf in DiffRingType 'M[E]_n matrix_diffRingMixin.

Lemma to_der (A : 'M[E]_n) : \\d A = \d A.
Proof. by []. Qed.

End SquareMatrix.

Lemma to_inv {R : comUnitRingType} {n} (A : 'M[R]_n.+1) : invmx A = A^-1.
Proof. by []. Qed.

Section UnitSquareMatrix.

Variable E : comUnitDiffRingType.

Variable n' : nat.
Local Notation n := n'.+1.

Canonical matrix_unitDiffRing := Eval hnf in [unitDiffRingType of 'M[E]_n].

End UnitSquareMatrix.

Require Import mxutil.
Import Notations.
Import DiffAlgebra.Exports.

Section ConstMatrix.

Variable R : ringType.
Variable E : diffAlgType R.
Variable m n r : nat.
Implicit Types C : 'M[R]_(m,n).
Implicit Types D : 'M[R]_(n,r).

Lemma dmc C : \\d (lift_to E C) = 0.
Proof.
  by apply/matrixP=> i j; rewrite !mxE linearZ /= der1 scaler0.
Qed.

Lemma dmcl C (A : 'M[E]_(_, r)) : \\d (lift C *m A) = lift C *m \\d A.
Proof.
  by rewrite dmM dmc mul0mx add0r.
Qed.

Lemma dmcr (A : 'M[E]_(r, _)) C : \\d (A *m lift C) = \\d A *m lift C.
Proof.
  by rewrite dmM dmc mulmx0 addr0.
Qed.

End ConstMatrix.

Section ConstScalar.

Variable R : ringType.
Variable E : diffAlgType R.
Variable m n r : nat.
Implicit Types A : 'M[E]_(m,n).

Local Notation "c *:: A" := (GRing.in_alg _ c *: A) (at level 40, left associativity) : ring_scope.

Lemma dmcs c A : \\d (c *:: A) = c *:: \\d A.
Proof.
  by apply/matrixP => i j; rewrite !mxE derM /= linearZ /= der1 scaler0 mul0r add0r.
Qed.

Lemma trmx_cscalemx c A : (c *:: A)^T = c *:: A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

End ConstScalar.

Section DerKronProd.

Variable E : comUnitDiffRingType.

Section Theory.

Variable m1 n1 m2 n2 : nat.
Implicit Types A : 'M[E]_(m1,n1).
Implicit Types B : 'M[E]_(m2,n2).

Lemma dm_delta m n i j : \\d (delta_mx i j) = 0 :> 'M[E]_(m,n).
Proof.
  apply/matrixP=> i' j'; rewrite !mxE /=.
  case (_ && _).
  - by rewrite der1.
  - by rewrite raddf0.
Qed.

Lemma dm_kron A B : \\d (A *o B) = \\d A *o B + A *o \\d B.
Proof.
  apply/matrixP=> i j; rewrite !mxE /=.
  case/mxvec_indexP: i => n1i n2i.
  case/mxvec_indexP: j => m1i m2i.
  by rewrite !vec_mx_delta !mxvecE map_trmx -map_mxE !dmM dm_delta mulmx0 addr0 !mxE.
Qed.

End Theory.

Section Corollaries.

Variable m n r : nat.
Implicit Types A : 'M[E]_(m,n).

Lemma dm_kron1mx A : \\d (I *o A) = (I : 'M_(r,_)) *o \\d A.
Proof.
  by rewrite dm_kron dmI kron0mx add0r.
Qed.

Lemma dm_kronmx1 A : \\d (A *o I) = \\d A *o (I : 'M_(_,r)).
Proof.
  by rewrite dm_kron dmI kronmx0 addr0.
Qed.

End Corollaries.

End DerKronProd.

Module Notations.

Notation "\\d" := (map_mx \d) : diff_scope.
Notation "c *:: A" := (GRing.in_alg _ c *: A) (at level 40, left associativity) : ring_scope.

End Notations.


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

Require Import mxlinear.
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

Import UnitDiffComAlgebra.Exports.

Section Paper.

(* Scalar type *)
Variable R : ringType.
(* Element type *)
Variable E : unitDiffComAlgType R.

Implicit Types c : R.

Section Definitions.

Variable m n : nat.
Implicit Types A : 'M[E]_(m, n).
Implicit Types B : 'M[E]_m.

Lemma test c A : \dm (c *:: A) = c *:: \dm A.
Proof. by rewrite linearZ. Qed.

Definition sym B := B^T + B.

Definition upinv_def c A := invmx (A^T *m A + c *:: 1%:M) *m A^T.
Fact upinv_key : unit. by done. Qed. 
Definition upinv := locked_with upinv_key upinv_def.
Canonical upinv_unlockable := [unlockable fun upinv].

Definition pinv := upinv 0.

End Definitions.

Notation "A ^- c" := (upinv c A) : ring_scope.

Section Appendix.

Variable m n' : nat.
Local Notation n := n'.+1.
Implicit Types A : 'M[E]_(m, n).
Implicit Types B : 'M[E]_n.

Variable A : 'M[E]_(m, n).
Variable u : R.

Local Notation "'invertable' B" := (B \is a GRing.unit) (at level 8).

Hypothesis h_invertable : invertable (A^T *m A + u *:: 1%:M).

Local Notation "A ^^-1" := (invmx A) (at level 8): ring_scope.
Notation "A ** B" := (A *m B) (at level 40, left associativity) : ring_scope.
Notation "\\d" := \dm.
Notation "u *** A" := (u *:: A) (at level 40, left associativity).
Notation I := 1%:M.

Lemma fold_upinv : (A^T ** A + u *** I)^-1 ** A^T = upinv u A.
Proof. by rewrite unlock. Qed.

Lemma to_inv B : B^^-1 = B^-1.
Proof. by done. Qed.

Lemma to_der_inv B : \\d (B^^-1) = \d (B^-1).
Proof. by done. Qed.

Lemma to_der1 : \\d I = \d 1 :> 'M[E]_n.
Proof. by done. Qed.

Lemma to_mulmx B1 B2 : B1 * B2 = B1 ** B2.
Proof. by done. Qed.

Lemma B_CA {Z : zmodType} (a b c : Z) : a + b + c = b + (c + a).
Proof. by rewrite addrA addrC addrA addrC addrA. Qed.

Lemma dm_upinv : \\d (A^-u) = -A^-u ** \\d A ** A^-u + (A^T ** A + u *** I)^-1 ** (\\d A)^T ** (I - A ** A^-u).
Proof.
  set (goal := _ + _) at 1.
  rewrite unlock dmM.
  rewrite to_der_inv der_inv.
  rewrite linearD /= linearZ /= to_der1 der1 scaler0 addr0 dmM.
  rewrite -mulmxA fold_upinv mulrDr mulmxDl !mulNr !mulNmx -mulNmx -mulNr !to_mulmx !mulmxA.
  by rewrite fold_upinv B_CA !mulNmx to_inv -!mulmxA -mulmxBr -{1}(mulmx1 (\\d A^T)) -mulmxBr !mulmxA -map_trmx -mulNmx -mulNmx.
  by done.
Qed.

End Appendix.

End Paper.

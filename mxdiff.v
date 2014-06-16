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

Module MxDiff.

(* Element type *)
Variable E : diffRingType.

Definition der_matrix m n (A : 'M[E]_(m, n)) := map_mx \d A.

Notation "\dm" := (@der_matrix _ _).

Section Util.
  Variable R : diffRingType.
  Lemma der_is_additive (a b : R) : \d (a - b) = \d a - \d b.
  Proof.
    by case: R a b => ? [] ? [].
  Qed.

  Canonical der_additive := Additive der_is_additive.

  Variable V : zmodType.

  Lemma sumr I r (P : pred I) (F1 F2 : I -> V) :
    \sum_(i <- r | P i) (F1 i + F2 i)
    = \sum_(i <- r | P i) F1 i + \sum_(i <- r | P i) F2 i.
  Proof. by rewrite -big_split /=. Qed.

End Util.

Section AnyMatrix.

Variable m n r : nat.
Implicit Types A : 'M[E]_(m, n).
Implicit Types B : 'M[E]_(n, r).

Lemma dm_product A B : \dm (A *m B) = \dm A *m B + A *m \dm B.
Proof.
  apply/matrixP => i k.
  rewrite !mxE.
  rewrite raddf_sum.
  rewrite -big_split.
  apply eq_bigr => j.
  rewrite !mxE.
  unfold der_additive.
  simpl.
  by rewrite der_prod.
Qed.

End AnyMatrix.

Section SquareMatrix.

(* Non-trival square matrices are differential unit rings *)

Variable n' : nat.
Local Notation n := n'.+1.

Definition matrix_unitDiffRingType := ?
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq div choice fintype.
Require Import finfun bigop prime binomial ssralg finset fingroup finalg.
Require Import perm zmodp.

Import GroupScope.
Import GRing.Theory.
Open Local Scope ring_scope.

Require Import matrix.

(* General matrix multiplication 'M[U]_(m,n) -> 'M[V]_(n,p) -> 'M[Z]_(m,p) *)
Section GeneralMul.

Variable U V : Type.
Variable Z : zmodType.
Variable mul : U -> V -> Z.

Fact gmulmx_key : unit. Proof. by []. Qed.
Definition gmulmx m n p (A : 'M[U]_(m, n)) (B : 'M[V]_(n, p)) : 'M[Z]_(m, p) :=
  \matrix[gmulmx_key]_(i, k) \sum_j (mul (A i j) (B j k)).

End GeneralMul.

Section GeneralDiag.

Variable V : zmodType.
Variable n : nat.

Fact gdiag_mx_key : unit. Proof. by []. Qed.
Definition gdiag_mx (d : 'rV[V]_n) :=
  \matrix[gdiag_mx_key]_(i, j) (if i == j then d 0 i else 0).

Fact gscalar_mx_key : unit. Proof. by []. Qed.
Definition gscalar_mx x : 'M[V]_n :=
  \matrix[gscalar_mx_key]_(i , j) (if i == j then x else 0).
Notation "x %:gM" := (gscalar_mx x) (at level 8): ring_scope.

Lemma gdiag_const_mx a : gdiag_mx (const_mx a) = a%:gM :> 'M_n.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

End GeneralDiag.

Local Notation "x %:gM" := (gscalar_mx _ x) (at level 8): ring_scope.

Lemma scalar_gscalar (R : ringType) n (x : R) : x%:M = x%:gM :> 'M_n.
Proof. by apply/matrixP=> i j; rewrite !mxE; case: (i == j). Qed.

Section LmoduleElem.

Variable R : ringType.
Variable V : lmodType R.

Fact lscalemx_key : unit. Proof. by []. Qed.
Definition lscalemx m n x (A : 'M[V]_(m,n)) := \matrix[lscalemx_key]_(i, j) (x *: A i j).
Local Notation "x *ml: A" := (lscalemx x A) (at level 40) : ring_scope.

Lemma lscale1mx m n (A : 'M[V]_(m,n)) : 1 *ml: A = A.
Proof. by apply/matrixP=> i j; rewrite !mxE scale1r. Qed.

Definition lmulmx := gmulmx (@GRing.scale _ V).
Notation "A *ml B" := (lmulmx A B) (at level 40, format "A  *ml  B") : ring_scope.

Lemma lmulmxA m n p q (A : 'M_(m, n)) (B : 'M_(n, p)) (C : 'M_(p, q)) : A *ml (B *ml C) = A *m B *ml C.
Proof.
apply/matrixP=> i l; rewrite !mxE.
transitivity (\sum_j (\sum_k (A i j *: (B j k *: C k l)))).
  by apply: eq_bigr => j _; rewrite mxE scaler_sumr.
rewrite exchange_big; apply: eq_bigr => j _; rewrite mxE scaler_suml /=.
by apply: eq_bigr => k _; rewrite scalerA.
Qed.

Lemma lmul_diag_mx m n d (A : 'M_(m, n)) :
  gdiag_mx d *ml A = \matrix_(i, j) (d 0 i *: A i j).
Proof.
apply/matrixP=> i j; rewrite !mxE (bigD1 i) //= mxE eqxx big1 ?addr0 // => i'.
rewrite mxE eq_sym.
move/negbTE->.
by rewrite scale0r.
Qed.

Lemma lmul_mx_diag m n (A : 'M_(m, n)) d :
  A *ml gdiag_mx d = \matrix_(i, j) (A i j *: d 0 j).
Proof.
apply/matrixP=> i j; rewrite !mxE (bigD1 j) //= mxE eqxx big1 ?addr0 // => i'.
rewrite mxE eq_sym.
move/negbTE->.
by rewrite scaler0.
Qed.

Lemma lmul_scalar_mx m n a (A : 'M_(m, n)) : a%:gM *ml A = a *ml: A.
Proof.
by rewrite -gdiag_const_mx lmul_diag_mx; apply/matrixP=> i j; rewrite !mxE.
Qed.

Lemma lmul1mx m n (A : 'M_(m, n)) : 1%:M *ml A = A.
Proof. by rewrite scalar_gscalar lmul_scalar_mx lscale1mx. Qed.

End LmoduleElem.

Local Notation "A *ml B" := (lmulmx A B) (at level 40, format "A  *ml  B") : ring_scope.

Local Notation "A ^cm" := (A : 'M[_^c]_(_,_)) (at level 2).
Lemma trmx_mul_c (R : ringType) m n p (A : 'M[R]_(m,n)) (B : 'M_(n,p)) : (A *m B)^T = B^cm^T *m A^cm^T.
Proof.
  apply/matrixP=> i l; rewrite !mxE.
  by apply eq_bigr => j ?; rewrite !mxE.
Qed.

Require Import bimodule.

Section RmoduleElem.

Variable R : ringType.
Variable V : rmodType R.

Definition rmulmx := gmulmx (@rscale _ V).

Notation "A *mr B" := (rmulmx A B) (at level 40, left associativity, format "A  *mr  B") : ring_scope.

Lemma rmulmx_lmulmx m n p (A : 'M_(m,n)) (B : 'M_(n,p)) : A *mr B = (B^cm^T *ml A^T)^T.
Proof.
apply/matrixP=> i l; rewrite !mxE.
by apply eq_bigr => j ?; rewrite !mxE.
Qed.

Lemma rmulmxA m n p q (A : 'M_(m, n)) (B : 'M_(n, p)) (C : 'M_(p, q)) : A *mr (B *m C) = A *mr B *mr C.
Proof.
  rewrite !rmulmx_lmulmx; f_equal.
  rewrite trmxK lmulmxA; f_equal.
  by rewrite (trmx_mul_c B C).
Qed.

Lemma rmulmx1 m n (A : 'M_(m, n)) : A *mr 1%:M = A.
Proof. 
  by rewrite rmulmx_lmulmx trmx1 lmul1mx trmxK.
Qed.

End RmoduleElem.

Module Notations.

Notation "A *ml B" := (lmulmx A B) (at level 40, format "A  *ml  B") : ring_scope.
Notation "A *mr B" := (rmulmx A B) (at level 40, left associativity, format "A  *mr  B") : ring_scope.

End Notations.
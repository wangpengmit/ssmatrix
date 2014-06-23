Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice fintype.
Require Import finfun bigop prime binomial.

Require Import matrix.
Require Import ssralg.
Import GRing.Theory.
Open Local Scope ring_scope.

Section Map2Matrix.

Variables (aT bT rT : Type) (f : aT -> bT -> rT).
Variable m n : nat.
Implicit Types A : 'M[aT]_(m,n).
Implicit Types B : 'M[bT]_(m,n).

Fact map2_mx_key : unit. Proof. by []. Qed.
Definition map2_mx A B := \matrix[map2_mx_key]_(i, j) f (A i j) (B i j).

End Map2Matrix.

(* Hadamard (element-wise) product *)
Local Notation elemprod := (map2_mx *%R).

(* Row-major vectorizatin *)
Local Notation rvec := mxvec.

(* Column-major vectorization *)
Local Notation vec A := (rvec A^T)^T.

Section KroneckerProduct.

(* mulmx_linear requires comRing, don't know why *)
Variable R : comRingType.
Variables m1 n1 m2 n2 : nat.
Implicit Types A : 'M[R]_(m1,n1).
Implicit Types B : 'M[R]_(m2,n2).

Definition kron A B := lin_mx ((mulmxr B) \o (mulmx A^T)).
Local Notation "A *o B" := (kron A B) (at level 40, left associativity).

Lemma kronP A B C : rvec C *m (A *o B) = rvec (A^T *m C *m B).
  by rewrite mul_vec_lin.
Qed.

End KroneckerProduct.

Local Notation "A *o B" := (kron A B) (at level 40, left associativity).

Require Import zmodp.

Section DeltaMxTheory.

Variable R : comRingType.
Variables m1 n1 m2 n2 : nat.
Implicit Types A : 'M[R]_(m1,n1).
Implicit Types B : 'M[R]_(m2,n2).

Lemma colE j A : col j A = A *m delta_mx j 0.
Proof.
  apply/colP=> i; rewrite !mxE (bigD1 j) //= mxE !eqxx mulr1.
  by rewrite big1 ?addr0 // => i' ne_i'i; rewrite mxE /= (negbTE ne_i'i) mulr0.
Qed.

Lemma rowcolE i j A B : A *m delta_mx i j *m B = col i A *m row j B.
Proof.
  by rewrite rowE colE !mulmxA -(mulmxA _ (delta_mx i 0)) mul_delta_mx.
Qed.

Lemma cVMrV m n (c : 'cV[R]_m) (r : 'rV_n) i j : (c *m r) i j = c i 0 * r 0 j.
Proof.
  by rewrite !mxE big_ord1.
Qed.

Lemma colMrowP i j A B ii jj : (col j A *m row i B) ii jj = A ii j * B i jj.
Proof.
  by rewrite cVMrV !mxE.
Qed.

End DeltaMxTheory.

Section KroneckerProductTheory.

Variable R : comRingType.

Section TrmxKron.

Variables m1 n1 m2 n2 : nat.
Implicit Types A : 'M[R]_(m1,n1).
Implicit Types B : 'M[R]_(m2,n2).

Lemma trmx_kron A B : (A *o B)^T = (A^T *o B^T).
Proof.
  apply/matrixP=> i j; rewrite !mxE trmxK /=.
  case/mxvec_indexP: i => n1i n2i.
  case/mxvec_indexP: j => m1i m2i.
  by rewrite !vec_mx_delta !mxvecE !rowcolE !colMrowP !mxE.
Qed.

End TrmxKron.

Section KronPColumn.

Variables m1 n1 m2 n2 : nat.
Implicit Types A : 'M[R]_(m1,n1).
Implicit Types C : 'M[R]_(m2,n2).

Lemma kronPc A B C : vec (A *m B *m C) = (C^T *o A) *m vec B.
Proof.
  by rewrite !trmx_mul !mulmxA -kronP !trmx_mul trmx_kron trmxK.
Qed.

End KronPColumn.

Section Corollaries.

Variables m n r : nat.
Implicit Types A : 'M[R]_(m,n).
Implicit Types B : 'M[R]_(n,r).

Local Notation I := (1%:M).

Corollary vec_kron A B : vec (A *m B) = (I *o A) *m vec B.
Proof.
  by rewrite -(mulmx1 (A *m B)) kronPc trmx1.
Qed.

Corollary vec_kron2 A B : vec (A *m B) = (B^T *o I) *m vec A.
Proof.
  by rewrite -(mul1mx (A *m B)) !mulmxA kronPc.
Qed.

Corollary kron_shift A B : (I *o A) *m vec B = (B^T *o I) *m vec A.
Proof.
  by rewrite -vec_kron vec_kron2.
Qed.

End Corollaries.

End KroneckerProductTheory.

Local Notation "A .* B" := (elemprod A B) (at level 40, left associativity).

Lemma cowP : forall (R : Type) (n : nat) (u v : 'cV[R]_n), (forall i, u i 0 = v i 0) <-> u = v.
Proof. by split=> [eq_uv | -> //]; apply/matrixP=> i j; rewrite ord1. Qed.

Lemma vec_elemprod {R : ringType} {m n} (A B : 'M[R]_(m,n)) : vec (A .* B) = diag_mx (vec A)^T *m vec B.
Proof.
  apply/cowP=> k; case/mxvec_indexP: k => i j.
  by rewrite mul_diag_mx !mxE !mxvecE !mxE.
Qed.

Module Notations.

Notation elemprod := (map2_mx *%R).
Notation rvec := mxvec.
Notation vec A := (rvec A^T)^T.
Notation "A *o B" := (kron A B) (at level 40, left associativity).
Notation "A .* B" := (elemprod A B) (at level 40, left associativity).

End Notations.
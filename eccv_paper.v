(* Matrix Differentiation Deductions in ECCV 2014 submitted paper from Andrew Fitzgibbon 
Written by: Peng Wang (wangp.thu@gmail.com)
*)

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

Require Import mxdiff.
Import UnitDiffComAlgebra.Exports.

Notation "A ^^-1" := (invmx A) (at level 8): ring_scope.
Notation "A ** B" := (A *m B) (at level 40, left associativity) : ring_scope.
Notation "\\d" := \dm : diff_scope.
Notation "u *** A" := (u *:: A) (at level 40, left associativity) : ring_scope.
Notation I := (1%:M).

Section Util.

Variable R : ringType.
Variable E : lalgType R.

Implicit Types u : R.

Variable m : nat.
Implicit Types B : 'M[E]_m.

Lemma trmx_gscalemx u B : (u *:: B)^T = u *:: B^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

End Util.

Section Sym.

Variable R : ringType.
Variable n : nat.
Implicit Types B : 'M[R]_n.

Definition sym B := B^T + B.

Lemma fold_sym B : B^T + B = sym B.
Proof. by []. Qed.

End Sym.

Section upinv.

Variable R : ringType.
(* invmx requires comRing, don't know why *)
Variable E : unitDiffComAlgType R.

Implicit Types u : R.
Variable m n : nat.
Implicit Types A : 'M[E]_(m, n).
Implicit Types B : 'M[E]_m.

Definition upinv_def u A := (A^T ** A + u *** I)^^-1 ** A^T.
Fact upinv_key : unit. by []. Qed. 
Definition upinv := locked_with upinv_key upinv_def.
Canonical upinv_unlockable := [unlockable fun upinv].

Definition pinv := upinv 0.

Notation "A ^- u" := (upinv u A) : ring_scope.

Lemma fold_upinv u A : (A^T ** A + u *** I)^^-1 ** A^T = A^-u.
Proof. by rewrite unlock. Qed.

Lemma fold_upinvT u A : A ** (A^T ** A + u *** I)^^-1 = (A^-u)^T.
Proof. 
  set goal := LHS.
  by rewrite unlock trmx_mul trmxK trmx_inv linearD /= trmx_mul trmxK trmx_gscalemx trmx1.
Qed.

End upinv.

Notation "A ^- u" := (upinv u A) : ring_scope.

Section Appendix.

(* Scalar type *)
Variable R : ringType.
(* Element type *)
Variable E : unitDiffComAlgType R.

Variable m n' : nat.
Local Notation n := n'.+1.
Implicit Types A : 'M[E]_(m, n).
Implicit Types B : 'M[E]_n.

Variable A : 'M[E]_(m, n).
Variable u : R.

Notation invertible B := (B \is a GRing.unit).

Hypothesis h_invertible : invertible (A^T ** A + u *** I).

Lemma to_inv B : B^^-1 = B^-1.
Proof. by []. Qed.

Lemma to_der B : \\d B = \d B.
Proof. by []. Qed.

Lemma to_der1 : \\d I = \d 1 :> 'M[E]_n.
Proof. by []. Qed.

Lemma to_mulmx B1 B2 : B1 * B2 = B1 ** B2.
Proof. by []. Qed.

Lemma B_CA {Z : zmodType} (a b c : Z) : a + b + c = b + (c + a).
Proof. by rewrite addrA addrC addrA addrC addrA. Qed.

Lemma AupinvA_sym : (A ** A^-u)^T = A ** A^-u.
Proof. by rewrite trmx_mul -fold_upinvT -fold_upinv mulmxA. Qed.

Lemma dm_upinv : \\d (A^-u) = -A^-u ** \\d A ** A^-u + (A^T ** A + u *** I)^-1 ** (\\d A)^T ** (I - A ** A^-u).
Proof.
  set goal := RHS.
  rewrite unlock dmM.
  rewrite !to_inv !to_der (der_inv h_invertible).
  rewrite linearD /= linearZ /= to_der1 der1 scaler0 addr0 dmM.
  rewrite -mulmxA fold_upinv mulrDr mulmxDl !mulNr !mulNmx -mulNmx -mulNr !to_mulmx !mulmxA.
  by rewrite fold_upinv B_CA !mulNmx -!mulmxA -mulmxBr -{1}(mulmx1 (\\d A^T)) -mulmxBr !mulmxA -map_trmx -mulNmx -mulNmx.
Qed.

Lemma dm_AupinvA : \\d (A ** A^-u) = sym ((I - A ** A^-u) ** \\d A ** A^-u).
Proof.
  set goal := RHS.
  rewrite dmM.
  rewrite dm_upinv !(mulmxDr A) !mulmxA !addrA mulmxN !mulNmx.
  rewrite fold_upinvT.
  rewrite !mulmxDr mulmx1 mulmxN !mulmxA !addrA.
  rewrite -trmx_mul -(mulmxA _ A) -{2}AupinvA_sym -trmx_mul -addrA -linearB /= addrC !mulmxA fold_sym.
  by rewrite -{1}(mul1mx (\\d A ** _)) -mulmxA -mulmxBl !mulmxA.
Qed.

End Appendix.

Section Map2Matrix.

Variables (aT bT rT : Type) (f : aT -> bT -> rT).
Variable m n : nat.
Implicit Types A : 'M[aT]_(m,n).
Implicit Types B : 'M[bT]_(m,n).

Fact map2_mx_key : unit. Proof. by []. Qed.
Definition map2_mx A B := \matrix[map2_mx_key]_(i, j) f (A i j) (B i j).

End Map2Matrix.

(* Hadamard (element-wise) product *)
Notation elemprod := (map2_mx *%R).

(* Row-major vectorizatin *)
Notation rvec := mxvec.

(* Column-major vectorization *)
Notation vec A := (rvec A^T)^T.

Section KroneckerProduct.

(* mulmx_linear requires comRing, don't know why *)
Variable R : comRingType.
Variables m1 n1 m2 n2 : nat.
Implicit Types A : 'M[R]_(m1,n1).
Implicit Types B : 'M[R]_(m2,n2).

Definition kron A B := lin_mx ((mulmxr B) \o (mulmx A^T)).
Notation "A *o B" := (kron A B) (at level 40, left associativity).

Lemma kronP A B C : rvec C ** (A *o B) = rvec (A^T ** C ** B).
  by rewrite mul_vec_lin.
Qed.

End KroneckerProduct.

Notation "A *o B" := (kron A B) (at level 40, left associativity).

Require Import zmodp.

Section DeltaMxTheory.

Variable R : comRingType.
Variables m1 n1 m2 n2 : nat.
Implicit Types A : 'M[R]_(m1,n1).
Implicit Types B : 'M[R]_(m2,n2).

Lemma colE j A : col j A = A ** delta_mx j 0.
Proof.
  apply/colP=> i; rewrite !mxE (bigD1 j) //= mxE !eqxx mulr1.
  by rewrite big1 ?addr0 // => i' ne_i'i; rewrite mxE /= (negbTE ne_i'i) mulr0.
Qed.

Lemma rowcolE i j A B : A ** delta_mx i j ** B = col i A ** row j B.
Proof.
  by rewrite rowE colE !mulmxA -(mulmxA _ (delta_mx i 0)) mul_delta_mx.
Qed.

Lemma cVMrV m n (c : 'cV[R]_m) (r : 'rV_n) i j : (c ** r) i j = c i 0 * r 0 j.
Proof.
  by rewrite !mxE big_ord1.
Qed.

Lemma colMrowP i j A B ii jj : (col j A ** row i B) ii jj = A ii j * B i jj.
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

Lemma kronPc A B C : vec (A ** B ** C) = (C^T *o A) ** vec B.
Proof.
  by rewrite !trmx_mul !mulmxA -kronP !trmx_mul trmx_kron trmxK.
Qed.

End KronPColumn.

Section Corollaries.

Variables m n r : nat.
Implicit Types A : 'M[R]_(m,n).
Implicit Types B : 'M[R]_(n,r).

Corollary vec_kron A B : vec (A ** B) = (I *o A) ** vec B.
Proof.
  by rewrite -(mulmx1 (A ** B)) kronPc trmx1.
Qed.

Corollary vec_kron2 A B : vec (A ** B) = (B^T *o I) ** vec A.
Proof.
  by rewrite -(mul1mx (A ** B)) !mulmxA kronPc.
Qed.

Corollary kron_shift A B : (I *o A) ** vec B = (B^T *o I) ** vec A.
Proof.
  by rewrite -vec_kron vec_kron2.
Qed.

End Corollaries.

End KroneckerProductTheory.

Notation "A .* B" := (elemprod A B) (at level 40, left associativity).

Lemma cowP : forall (R : Type) (n : nat) (u v : 'cV[R]_n), (forall i, u i 0 = v i 0) <-> u = v.
Proof. by split=> [eq_uv | -> //]; apply/matrixP=> i j; rewrite ord1. Qed.

Lemma vec_elemprod {R : ringType} {m n} (A B : 'M[R]_(m,n)) : vec (A .* B) = diag_mx (vec A)^T ** vec B.
Proof.
  apply/cowP=> k; case/mxvec_indexP: k => i j.
  by rewrite mul_diag_mx !mxE !mxvecE !mxE.
Qed.

Section Section3.

(* Constants *)
Variable C : ringType.
(* Variables *)
Variable E : unitDiffComAlgType C.

Variable m' n' r' : nat.
Local Notation m := m'.+1.
Local Notation n := n'.+1.
Local Notation r := r'.+1.
(* W : weight matrix 
   M : target matrix *)
Variable cW cM : 'M[C]_(m, n).
Notation W := (\liftm cW).
Notation M := (\liftm cM).
Variable U : 'M[E]_(m, r).
Variable V : 'M[E]_(n, r).
Notation "~W" := (diag_mx (vec W)^T).
Notation "\m" := (vec M).
Notation "~U" := (I *o U).

Lemma eq_10_13 : vec (W .* (M - U ** V^T)) = ~W ** \m - ~W ** ~U ** vec V^T.
Proof.
  set goal := RHS.
  rewrite vec_elemprod.
  rewrite !raddfB /=.
  by rewrite vec_kron !mulmxA.
Qed.

End Section3.


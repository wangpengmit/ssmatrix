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

Require Import kronprod.
Import Notations.

Require Import eccv_paper_appendix.

Section ConstantMatrix.

Variable R : ringType.
Variable E : unitDiffComAlgType R.
Variable m n r : nat.
Implicit Types C : 'M[R]_(m,n).
Notation "\liftm" := (liftm E).

Lemma lift_mul C1 (C2 : 'M_(_, r)) : \liftm (C1 *m C2) = \liftm C1 *m \liftm C2.
Proof.
  apply/matrixP=> i j; rewrite !mxE /liftm raddf_sum.
  apply eq_bigr => k.
  by rewrite !mxE -scalerAl mul1r scalerA.
Qed.

Lemma lift_vec C : \liftm (vec C) = vec (\liftm C).
  by rewrite map_trmx -map_mxvec map_trmx.
Qed.

Lemma dmc C : \\d (\liftm C) = 0.
Proof.
  by apply/matrixP=> i j; rewrite !mxE linearZ /= der1 scaler0.
Qed.

Lemma dmcl C (A : 'M_(_, r)) : \\d (\liftm C *m A) = \liftm C *m \\d A.
Proof.
  by rewrite dmM dmc mul0mx add0r.
Qed.

Lemma dmcr (A : 'M_(r, _)) C : \\d (A *m \liftm C) = \\d A *m \liftm C.
Proof.
  by rewrite dmM dmc mulmx0 addr0.
Qed.

End ConstantMatrix.

Lemma map_mxE {aT rT} {f : aT -> rT} {m n} (A : 'M_(m,n)) i j : (map_mx f A) i j = f (A i j).
Proof. by rewrite !mxE /=. Qed.

Section DerKronProd.

Variable E : comUnitDiffRingType.

Section dm_kron.

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

End dm_kron.

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

End DerKronProd.

Section ColumnVectorToMatrix.

Variable E : Type.

Definition cvec_mx m n (v : 'cV[E]_(n * m)) : 'M_(m,n) := (vec_mx v^T)^T.

Lemma cvec_mxK m n c : vec (@cvec_mx m n c) = c.
Proof.
  by rewrite trmxK vec_mxK trmxK.
Qed.

End ColumnVectorToMatrix.

Section TransPerm.

Variable E : comRingType.

Variable m n : nat.

Definition trT := (lin_mx (@trmx E m n))^T.

Lemma trTP A : rvec A *m trT^T = rvec A^T.
  by rewrite trmxK mul_vec_lin.
Qed.

Lemma trTPc A : trT ** vec A = vec A^T.
Proof.
  by apply trmx_inj; rewrite !trmx_mul (trmxK (rvec A^T)) trTP !trmxK.
Qed.

End TransPerm.

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
Notation "~W" := (diag_mx (vec W)^T).
Notation "\m" := (vec M).
Notation "~U" := (I *o U).

Lemma eq_10_13 V : vec (W .* (M - U ** V^T)) = ~W ** \m - ~W ** ~U ** vec V^T.
Proof.
  set goal := RHS.
  rewrite vec_elemprod.
  rewrite !raddfB /=.
  by rewrite vec_kron !mulmxA.
Qed.

Variable v : C.

Definition eps1 := ~W ** \m - ~W ** ~U ** (~W ** ~U)^-v ** ~W ** \m.
Notation H := (I - ~W ** ~U ** (~W ** ~U)^-v).

Notation invertible B := (B \is a GRing.unit).

Hypothesis h_invertible : invertible ((~W ** ~U)^T ** (~W ** ~U) + v *** I).

Lemma dmWmr {p} (A : 'M[E]_(p, _)) : \\d (A ** ~W ** \m) = \\d A ** ~W ** \m.
Proof.
  by rewrite -!lift_vec /liftm map_trmx -map_diag_mx /= !dmcr.
Qed.

Lemma dmWl {p} (A : 'M[E]_(_, p)) : \\d (~W ** A) = ~W ** \\d A.
Proof.
  by rewrite -!lift_vec /liftm map_trmx -map_diag_mx /= !dmcl.
Qed.

Lemma eq_20_26 : \\d eps1 = 0 - H ** ~W ** (I *o \\d U) ** ((~W ** ~U)^-v ** ~W ** \m) - ((~W ** ~U)^-v)^T ** (I *o (\\d U)^T) ** (~W^T ** H ** ~W ** \m).
Proof.
  set goal := RHS.
  rewrite raddfB /= -(mul1mx (~W ** \m)) !mulmxA !dmWmr to_der der1 !mul0mx.
  rewrite (dm_AupinvA h_invertible). (* (22) *)
  rewrite dmWl (dm_kron1mx _ U) !mulmxA. (* (25) *)
  by rewrite /sym (addrC _^T) !trmx_mul (trmx_kron I (\\d U)) raddfB /= AupinvA_sym !trmx1 !mulmxA (mulmxDl _ _ ~W) (mulmxDl _ _ \m) opprD addrA -(mulmxA _ _ ~W) -(mulmxA _ _ \m) -(mulmxA _ _ H) -(mulmxA _ _ ~W) -(mulmxA _ (_ ** _) \m).
Qed.

Notation "V*" := ((cvec_mx ((~W ** ~U)^-v ** ~W ** \m))^T).

Lemma to_Vstar : (~W ** ~U)^-v ** ~W ** \m = vec V*^T.
Proof.
  by rewrite (trmxK V*) cvec_mxK.
Qed.

Notation R := (W .* (M - U ** V*^T)).

Lemma eq_28_31 : ~W^T ** H ** ~W ** \m = vec (W .* R).
Proof.
  set goal := RHS.
  rewrite mulmxBr !mulmxBl !mulmxA mulmx1.
  rewrite -(mulmxA _ _ ~W) -(mulmxA _ (_ ** _) \m) to_Vstar.
  rewrite -!mulmxA -mulmxBr !mulmxA -eq_10_13.
  by rewrite tr_diag_mx -vec_elemprod.
Qed.

Notation "~V*" := (V* *o I).
Notation T := (trT _ _ _).

Lemma map_vec aT rT (f : aT -> rT) m n (A : 'M_(m,n)) : map_mx f (vec A) = vec (map_mx f A).
Proof.
  by rewrite map_trmx -map_mxvec map_trmx.
Qed.

Lemma eq_32_35 : \\d eps1 = - (H ** ~W ** ~V* + ((~W ** ~U)^-v)^T ** ((W .* R)^T *o I) ** T) ** \\d (vec U).
Proof.
  set goal := RHS.
  rewrite eq_20_26 eq_28_31 {1}to_Vstar.
  rewrite -(mulmxA _ _ (vec _)) kron_shift (trmxK V*) -(mulmxA _ _ (vec (_ .* _))) kron_shift !mulmxA.
  by rewrite -trTPc !mulmxA -(mul0mx _ (vec (\\d U))) -!mulmxBl sub0r -opprD -map_vec.
Qed.

End Section3.


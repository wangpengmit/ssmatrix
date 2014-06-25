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

Require Import diffalg.
Import DiffRing.Exports.
Import UnitDiffRing.Exports.
Import ComUnitDiffRing.Exports.
Import UnitDiffComAlgebra.Exports.
Open Local Scope diff_scope.

Require Import mxutil.
Import Notations.
Require Import mxdiff.
Import Notations.
Require Import eccv_paper_appendix.

Lemma map_mxE {aT rT} {f : aT -> rT} {m n} (A : 'M_(m,n)) i j : (map_mx f A) i j = f (A i j).
Proof. by rewrite !mxE /=. Qed.

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
Notation W := (lift cW).
Notation M := (lift cM).
Variable U : 'M[E]_(m, r).
Notation "~W" := (diag_mx (vec W)^T).
Notation "\m" := (vec M).
Notation "~U" := (I *o U).

Lemma eq_10_13 V : vec (W .* (M - U *m V^T)) = ~W *m \m - ~W *m ~U *m vec V^T.
Proof.
  set goal := RHS.
  rewrite vec_elemprod.
  rewrite !raddfB /=.
  by rewrite vec_kron !mulmxA.
Qed.

Variable v : C.

Definition eps1 := ~W *m \m - ~W *m ~U *m (~W *m ~U)^-v *m ~W *m \m.
Notation H := (I - ~W *m ~U *m (~W *m ~U)^-v).
Notation invertible B := (B \is a GRing.unit).
Hypothesis h_invertible : invertible (mupinv_core v (~W *m ~U)).

Lemma dmmr {p} (A : 'M[E]_(p, _)) : \\d (A *m \m) = \\d A *m \m.
Proof.
  by rewrite -!lift_vec !dmcr.
Qed.

Lemma dmWr {p} (A : 'M[E]_(p, _)) : \\d (A *m ~W) = \\d A *m ~W.
Proof.
  by rewrite -!lift_vec map_trmx -map_diag_mx !dmcr.
Qed.

Lemma dmWl {p} (A : 'M[E]_(_, p)) : \\d (~W *m A) = ~W *m \\d A.
Proof.
  by rewrite -!lift_vec map_trmx -map_diag_mx !dmcl.
Qed.

Lemma eq_20_26 : \\d eps1 = 0 - H *m ~W *m (I *o \\d U) *m ((~W *m ~U)^-v *m ~W *m \m) - ((~W *m ~U)^-v)^T *m (I *o (\\d U)^T) *m (~W^T *m H *m ~W *m \m).
Proof.
  set goal := RHS.
  rewrite raddfB /= -(mul1mx (~W *m \m)) !mulmxA !dmmr !dmWr dmI !mul0mx.
  rewrite (dm_AmupinvA h_invertible). (* (22) *)
  rewrite dmWl (dm_kron1mx _ U) !mulmxA. (* (25) *)
  by rewrite /sym (addrC _^T) !trmx_mul (trmx_kron I (\\d U)) raddfB /= AmupinvA_sym !trmx1 !mulmxA (mulmxDl _ _ ~W) (mulmxDl _ _ \m) opprD addrA -(mulmxA _ _ ~W) -(mulmxA _ _ \m) -(mulmxA _ _ H) -(mulmxA _ _ ~W) -(mulmxA _ (_ *m _) \m).
Qed.

Notation "V*" := ((cvec_mx ((~W *m ~U)^-v *m ~W *m \m))^T).

Lemma to_Vstar : (~W *m ~U)^-v *m ~W *m \m = vec V*^T.
Proof.
  by rewrite (trmxK V*) cvec_mxK.
Qed.

Notation R := (W .* (M - U *m V*^T)).

Lemma eq_28_31 : ~W^T *m H *m ~W *m \m = vec (W .* R).
Proof.
  set goal := RHS.
  rewrite mulmxBr !mulmxBl !mulmxA mulmx1.
  rewrite -(mulmxA _ _ ~W) -(mulmxA _ (_ *m _) \m) to_Vstar.
  rewrite -!mulmxA -mulmxBr !mulmxA -eq_10_13.
  by rewrite tr_diag_mx -vec_elemprod.
Qed.

Notation "~V*" := (V* *o I).
Notation T := (trT _ _ _).

Lemma eq_32_35 : \\d eps1 = - (H *m ~W *m ~V* + ((~W *m ~U)^-v)^T *m ((W .* R)^T *o I) *m T) *m \\d (vec U).
Proof.
  set goal := RHS.
  rewrite eq_20_26 eq_28_31 {1}to_Vstar.
  rewrite -(mulmxA _ _ (vec _)) kron_shift (trmxK V*) -(mulmxA _ _ (vec (_ .* _))) kron_shift !mulmxA.
  by rewrite -trTPc !mulmxA -(mul0mx _ (vec (\\d U))) -!mulmxBl sub0r -opprD -(map_vec _ U).
Qed.

End Section3.


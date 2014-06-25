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
Import Notations.

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


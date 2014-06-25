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

Section Sym.

Variable R : ringType.
Variable n : nat.
Implicit Types B : 'M[R]_n.

Definition sym B := B^T + B.

Lemma fold_sym B : B^T + B = sym B.
Proof. by []. Qed.

End Sym.

Section MuPseudoinverse.

Variable R : ringType.
(* invmx requires comRing, don't know why *)
Variable E : unitDiffComAlgType R.

Implicit Types u : R.
Variable m n : nat.
Implicit Types A : 'M[E]_(m, n).
Implicit Types B : 'M[E]_m.

Definition mupinv_core u A := A^T *m A + u *:: I.
Definition mupinv_def u A := (mupinv_core u A)^^-1 *m A^T.
Fact mupinv_key : unit. by []. Qed. 
Definition mupinv := locked_with mupinv_key mupinv_def.
Canonical mupinv_unlockable := [unlockable fun mupinv].

Definition pinv := mupinv 0.

Local Notation "A ^- u" := (mupinv u A) : ring_scope.

Lemma fold_mupinv u A : (A^T *m A + u *:: I)^^-1 *m A^T = A^-u.
Proof. by rewrite unlock. Qed.

Lemma fold_mupinvT u A : A *m (A^T *m A + u *:: I)^^-1 = (A^-u)^T.
Proof. 
  set goal := LHS.
  by rewrite unlock trmx_mul trmxK trmx_inv linearD /= trmx_mul trmxK trmx_cs trmx1.
Qed.

End MuPseudoinverse.

Local Notation "A ^- u" := (mupinv u A) : ring_scope.

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

Hypothesis h_invertible : invertible (mupinv_core u A).

Lemma AmupinvA_sym : (A *m A^-u)^T = A *m A^-u.
Proof. by rewrite trmx_mul -fold_mupinvT -fold_mupinv mulmxA. Qed.

Lemma dm_mupinv : \\d (A^-u) = 0 - A^-u *m \\d A *m A^-u + (A^T *m A + u *:: I)^-1 *m (\\d A)^T *m (I - A *m A^-u).
Proof.
  set goal := RHS.
  rewrite unlock dmM /mupinv_core.
  rewrite !invmx_inv !dm_der (der_inv h_invertible) /mupinv_core -!invmx_inv -!dm_der.
  rewrite raddfD /= dmcs dmI scaler0 addr0 dmM.
  rewrite -mulmxA fold_mupinv mulrDr mulmxDl -!mulmxE !mulNmx !mulmxA.
  by rewrite fold_mupinv -addrA (addrC _ (_ *m _)) !addrA (addrC (-_)) -(mulmxA _ _ (A^-u)) -mulmx1Br -map_trmx addrC -sub0r.
Qed.

Lemma dm_AmupinvA : \\d (A *m A^-u) = sym ((I - A *m A^-u) *m \\d A *m A^-u).
Proof.
  set goal := RHS.
  rewrite dmM.
  rewrite dm_mupinv sub0r !(mulmxDr A) !mulmxA !addrA mulmxN.
  rewrite fold_mupinvT.
  rewrite !mulmxDr mulmx1 mulmxN !mulmxA !addrA.
  rewrite -trmx_mul -(mulmxA _ A) -!mulmxA -AmupinvA_sym !mulmxA -trmx_mul -addrA -linearB /= addrC !mulmxA fold_sym.
  by rewrite -mulmxA -mul1Brmx !mulmxA.
Qed.

End Appendix.

Module Notations.

Notation "A ^- u" := (mupinv u A) : ring_scope.

End Notations.
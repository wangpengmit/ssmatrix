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

Lemma B_CA {Z : zmodType} (a b c : Z) : a + b + c = b + (c + a).
Proof. by rewrite addrA addrC addrA addrC addrA. Qed.

Lemma AupinvA_sym : (A ** A^-u)^T = A ** A^-u.
Proof. by rewrite trmx_mul -fold_upinvT -fold_upinv mulmxA. Qed.

Lemma dm_upinv : \\d (A^-u) = -A^-u ** \\d A ** A^-u + (A^T ** A + u *** I)^-1 ** (\\d A)^T ** (I - A ** A^-u).
Proof.
  set goal := RHS.
  rewrite unlock dmM.
  rewrite !to_inv !to_der (der_inv h_invertible).
  rewrite linearD /= linearZ /= !to_der der1 scaler0 addr0 -!to_der dmM.
  rewrite -mulmxA fold_upinv mulrDr mulmxDl !mulNr !mulNmx -mulNmx -mulNr -!mulmxE !mulmxA.
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
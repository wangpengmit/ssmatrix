(* (c) Copyright ? *)

(*****************************************************************************
  Matrix derivation (differentiation).

       \\d A == element-wise derivation of matrix A : 'M[R]_(m,n), where R
                must have a diffRingType structure. Equivalent to (map_mx \d A).
      c :: A == Constant scale: lift c : R into E : lalgType R, then scale 
                matrix A by it. Equivalent to (c *: 1 *: A). The significance 
                of this operation is that matrix derivation is commutative with
                it. 
                (Matrix derivation is actually scalable (hence linear) for 
                this constant-scale operation, but we didn't register a linear
                canonical structure for it, because that requires a 
                lmodType canonical structure on matrices for this constant-scale,
                whereas SSReflect has already registered a matrix_lmodType for 
                scalemx and Coq doesn't allow overwriting canonical structure 
                registration.)
 lift_to E A == lift A : 'M[R]_(m,n) to 'M[E]_(m,n), where E : lalgType R.
                Matrix derivation is commutative with multiplication by a 
                (lifted) constant matrix.
      lift A == lift_to _ A

  The main results about matrix derivation are:
      dmM :      \\d (A *m B) = \\d A *m B + A *m \\d B
      dmI :             \\d I = 0
      dmc :      \\d (lift C) = 0
     dmcs :     \\d (c *:: A) = c *:: \\d A      
     dmcl : \\d (lift C *m A) = lift C *m \\d A  (and the symmetric version dmcr)
  dm_kron :      \\d (A *o B) = \\d A *o B + A *o \\d B

  Non-empty square matrices inherit the diffRingType (or unitDiffRingType) 
  structure of their elements.

******************************************************************************)

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
Import DiffAlgebra.Exports.
Open Local Scope diff_scope.

Require Import mxutil.
Import Notations.

Local Notation "\\d" := (map_mx \d) : diff_scope.

Section AnyMatrix.

(* Element type *)
Variable E : diffRingType.

Variable m n r : nat.
Implicit Types A : 'M[E]_(m, n).
Implicit Types B : 'M[E]_(n, r).

(* Matrix derivation is derivative (has Lebniz product rule) for matrix multiplication *)
Lemma dmM A B : \\d (A *m B) = \\d A *m B + A *m \\d B.
Proof.
  by apply/matrixP => i k; rewrite !mxE !raddf_sum -big_split; apply eq_bigr => j; rewrite /= !mxE derM.
Qed.

End AnyMatrix.

Lemma dmI {E : diffRingType} {n} : \\d I = 0 :> 'M[E]_n.
Proof.
  apply: (addIr (\\d (I *m I))).
  rewrite add0r {1}mul1mx.
    by rewrite dmM mulmx1 mul1mx.
Qed.

Section SquareMatrix.

Variable E : diffRingType.

Variable n' : nat.
Local Notation n := n'.+1.

(* Can only register for derivative here because derivative is only defined for rings, not graded rings *)
Import Derivative.Exports.
Canonical dm_derivative := Derivative (@dmM E n n n).

Definition matrix_diffRingMixin := DiffRingMixin (@dmM E n n n).
Canonical matrix_diffRingType := Eval hnf in DiffRingType 'M[E]_n matrix_diffRingMixin.

Lemma dm_der (A : 'M[E]_n) : \\d A = \d A.
Proof. by []. Qed.

End SquareMatrix.

Section UnitSquareMatrix.

(* invmx requires comRing, don't know why *)
Variable E : comUnitDiffRingType.

Variable n' : nat.
Local Notation n := n'.+1.

Canonical matrix_unitDiffRing := Eval hnf in [unitDiffRingType of 'M[E]_n].

End UnitSquareMatrix.

(* Scale by constant, which is commutative with matrix derivation *)
Section ConstScale.

Variable R : ringType.
Variable E : diffAlgType R.
Variable m n r : nat.
Implicit Types A : 'M[E]_(m,n).

Local Notation "c *:: A" := (GRing.in_alg _ c *: A) (at level 40, left associativity) : ring_scope.

Lemma dmcs c A : \\d (c *:: A) = c *:: \\d A.
Proof.
  by apply/matrixP => i j; rewrite !mxE derM /= linearZ /= der1 scaler0 mul0r add0r.
Qed.

Lemma trmx_cs c A : (c *:: A)^T = c *:: A^T.
Proof. by apply/matrixP=> i j; rewrite !mxE. Qed.

End ConstScale.

(* Lift a matrix of 'M[R]_(m,n) into 'M[E]_(m,n), where E : lalgTyp R *)
Section Lift.

Variable R : ringType.
Variable E : lalgType R.
Variable m n r : nat.
Implicit Types C : 'M[R]_(m,n).
Implicit Types D : 'M[R]_(n,r).

Notation lift := (map_mx (in_alg E)).

Lemma lift_mul C D : lift (C *m D) = lift C *m lift D.
Proof.
  apply/matrixP=> i j; rewrite !mxE raddf_sum.
  apply eq_bigr => k.
  by rewrite !mxE -scalerAl mul1r scalerA.
Qed.

Lemma lift_vec C : lift (vec C) = vec (lift C).
  by rewrite map_vec.
Qed.

End Lift.

Local Notation lift := (map_mx (in_alg _)).
Local Notation lift_to E := (map_mx (in_alg E)).

(* Matrix derivation is commutative with multiplication by a (lifted) constant matrix *)
Section DmLift.

Variable R : ringType.
Variable E : diffAlgType R.
Variable m n r : nat.
Implicit Types C : 'M[R]_(m,n).
Implicit Types D : 'M[R]_(n,r).

Lemma dmc C : \\d (lift_to E C) = 0.
Proof.
  by apply/matrixP=> i j; rewrite !mxE linearZ /= der1 scaler0.
Qed.

Lemma dmcl C (A : 'M[E]_(_, r)) : \\d (lift C *m A) = lift C *m \\d A.
Proof.
  by rewrite dmM dmc mul0mx add0r.
Qed.

Lemma dmcr (A : 'M[E]_(r, _)) C : \\d (A *m lift C) = \\d A *m lift C.
Proof.
  by rewrite dmM dmc mulmx0 addr0.
Qed.

End DmLift.

Section DerKronProd.

Variable E : comUnitDiffRingType.

Section Main.

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

(* Matrix derivation is also derivative (has Lebniz product rule) for Kronecker product, like it is for matrix multiplication *)
Lemma dm_kron A B : \\d (A *o B) = \\d A *o B + A *o \\d B.
Proof.
  apply/matrixP=> i j; rewrite !mxE /=.
  case/mxvec_indexP: i => n1i n2i.
  case/mxvec_indexP: j => m1i m2i.
  by rewrite !vec_mx_delta !mxvecE map_trmx -map_mxE !dmM dm_delta mulmx0 addr0 !mxE.
Qed.

End Main.

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

Module Notations.

Notation "\\d" := (map_mx \d) : diff_scope.
Notation "c *:: A" := (GRing.in_alg _ c *: A) (at level 40, left associativity) : ring_scope.
Notation lift := (map_mx (in_alg _)).
Notation lift_to E := (map_mx (in_alg E)).

End Notations.


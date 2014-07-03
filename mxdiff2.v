(* (c) Copyright ? *)

(*****************************************************************************
  Matrix derivation (differentiation).

******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice fintype.
Require Import finfun bigop prime binomial.

Require Import ssralg.
Import GRing.Theory.
Open Local Scope ring_scope.

Require Import matrix.

Require Import mxutil.
Import Notations.
Require Import bimodule.
Require Import derivation.
Require Import mxmodule.
Import Notations.

Section Ring.

(* Element type *)
Variable E : ringType.
Variable D : bimodType E E.
Variable der : {derAdd D}.

Notation "\d" := der.
Notation "\\d" := (@map_mx _ _ \d _ _).

Section AnyMatrix.

Variable m n r : nat.
Implicit Types A : 'M[E]_(m, n).
Implicit Types B : 'M[E]_(n, r).

(* Matrix derivation is derivative (has Lebniz product rule) for matrix multiplication *)
Lemma dmM A B : \\d (A *m B) = \\d A *mr B + A *ml \\d B.
Proof.
  by apply/matrixP => i k; rewrite !mxE !raddf_sum -big_split; apply eq_bigr => j; rewrite /= !mxE derM.
Qed.

End AnyMatrix.

Lemma dmI n : \\d I = 0 :> 'M_n.
Proof.
  apply: (addIr (\\d (I *m I))).
  by rewrite add0r {1}mul1mx dmM lmul1mx rmulmx1.
Qed.

(*here*)

Section SquareMatrix.

Variable n' : nat.
Local Notation n := n'.+1.

(* Can only register for DerMorph here because DerMorph is only defined for rings, not graded rings *)
Canonical dm_der := DerMorphFor 'M[D]_n^m (@dmM n n n).
(* Now that \\d has a canonical DerMorph structure, and since it already has a canonical Additive structure thanks to map_mx_additive, packDerAdd will automatically generate a DerAdd structure *)
Canonical dm_derAdd := packDerAdd 'M[D]_n^m \\d.

End SquareMatrix.

End Ring.

Section Lalgebra.

Variable R : ringType.
Variable E : lalgType R.
Variable D : bimodType E E.
Variable der : {linearDer E -> D}.

Notation "\d" := der.
Notation "\\d" := (@map_mx _ _ \d _ _).

Lemma dmcs m c (A : 'M[E]_m) : \\d (c *ml: A) = c%:A *ml: \\d A .
Proof. by apply/matrixP => i j; rewrite !mxE linearZ /=. Qed.

Lemma dmscale m c (A : 'M[E]_m) : \\d (c *ml: A) = (c *ml: I) *ml \\d A.
Proof. 
  by rewrite dmcs -lmul_scalar_mx -scalar_gscalar -scalemx1 scale_lscale.
Qed.

Variable n' : nat.
Local Notation n := n'.+1.

Lemma dmscale' c (A : 'M[E]_n^s) : \\d (c *: A) = c *: (1 : 'M[E]_n^s) *: (\\d A : 'M[D]_n^m).
Proof. by rewrite dmscale. Qed.

Canonical dm_scale := AddScale ('M[E]_n^s -> 'M[D]_n^m) dmscale'.

End Lalgebra.

Section DerKronProd.

Variable E : comRingType.
Variable D : comBimodType E.
Variable der : {derMorph D}.
Notation "\d" := (DerMorph.apply der).
Notation "\\d" := (map_mx \d).

(*
Section Main.

Lemma dm_delta m n i j : \\d (delta_mx i j) = 0 :> 'M[V]_(m,n).
Proof.
  apply/matrixP=> i' j'; rewrite !mxE /=.
  case (_ && _).
  - by rewrite der1.
  - by rewrite raddf0.
Qed.

Variable m1 n1 m2 n2 : nat.
Implicit Types A : 'M[E]_(m1,n1).
Implicit Types B : 'M[E]_(m2,n2).

(* Matrix derivation is also derivative (has Lebniz product rule) for Kronecker product, like it is for matrix multiplication *)
Lemma dm_kron A B : \\d (A *o B) = \\d A *o B + A *o \\d B.
Proof.
  apply/matrixP=> i j; rewrite !mxE /=.
  case/mxvec_indexP: i => n1i n2i.
  case/mxvec_indexP: j => m1i m2i.
  by rewrite !vec_mx_delta !mxvecE map_trmx -map_mxE !dmM dm_delta mulmx0 addr0 !mxE.
Qed.

End Main.
*)
Section Corollaries.

Variable m n r : nat.
Implicit Types A : 'M[E]_(m,n).

Lemma dm_lkron1mx A : \\d (I *o A) = (I : 'M_(r,_)) *ol \\d A.
Proof.
  apply/matrixP => i j.
  rewrite mxE.
  case/mxvec_indexP: i => n1i n2i.
  case/mxvec_indexP: j => m1i m2i.
  rewrite kronE.
  rewrite lkronE.
  rewrite derM.
  rewrite !mxE.
  case (_ == _).
  - by rewrite der1 /rscale scaler0 add0r.
  - by rewrite der0 /rscale scaler0 add0r.
Qed.

End Corollaries.

End DerKronProd.

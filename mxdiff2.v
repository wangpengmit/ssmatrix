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

Lemma dmscale m c (A : 'M[E]_m) : \\d (c *ml: A) = (c *ml: I) *ml \\d A .
Proof. 
  by rewrite dmcs -lmul_scalar_mx -scalar_gscalar -scalemx1 scale_gscale.
Qed.

Variable n' : nat.
Local Notation n := n'.+1.

Lemma dmscale' c (A : 'M[E]_n^s) : \\d (c *: A) = c *: (1 : 'M[E]_n^s) *: (\\d A : 'M[D]_n^m).
Proof. by rewrite dmscale. Qed.

Canonical dm_scale := AddScale ('M[E]_n^s -> 'M[D]_n^m) dmscale'.

End Lalgebra.
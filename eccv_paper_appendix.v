(* (c) Copyright ? *)

(*****************************************************************************
  Verification of formula deductions in the appendix of paper "Exact-Wiberg 
  Algorithm for Matrix Factorization with Missing Data" (ECCV 2014 submission)

  Main definitions:
            sym A == A^T + A. A must be a square matrix.
  mupinv_core u A == A^T *m A + u *ml: I
           A ^- u == (mupinv_core u A)^^-1 *m A^T
                  == (A^T *m A + u *ml: I)^^-1 *m A^T
                     The mu-pseudoinverse.
           pinv A == A ^- 0

  Main results: 
        dm_mupinv : 
        \\d (A^-u) = 0 - A^-u *ml \\d A *mr A^-u + (A^T *m A + u *ml: I)^-1 
                     *ml (\\d A)^T *mr (I - A *m A^-u)
                     The first result in Appendix A.
      dm_AmupinvA : 
   \\d (A *m A^-u) = sym ((I - A *m A^-u) *ml \\d A *mr A^-u)
                     The second result in Appendix A.

  All results are under the assumption: invertible (mupinv_core u A)).
  Sometimes I write (0 - a *m b) instead of (- a *m b) because the unary minus 
  sign binds tighter than *m, which I find counter-intuitive.

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

Require Import mxutil.
Import Notations.
Require Import bimodule.
Require Import derivation.
Require Import mxmodule.
Import Notations.
Require Import mxdiff.

Section Sym.

Variable V : zmodType.
Variable n : nat.
Implicit Types A : 'M[V]_n.

Definition sym A := A^T + A.

Lemma fold_sym A : A^T + A = sym A.
Proof. by []. Qed.

End Sym.

Section MuPseudoinverse.

Variable R : ringType.
(* invmx requires comRing *)
Variable E : unitComAlgType R.

Implicit Types u : R.
Variable m n : nat.
Implicit Types A : 'M[E]_(m, n).
Implicit Types B : 'M[E]_m.

Definition mupinv_core u A := A^T *m A + u *ml: I.
Definition mupinv_def u A := (mupinv_core u A)^^-1 *m A^T.
Fact mupinv_key : unit. by []. Qed. 
Definition mupinv := locked_with mupinv_key mupinv_def.
Canonical mupinv_unlockable := [unlockable fun mupinv].

Local Notation "A ^- u" := (mupinv u A) : ring_scope.

Lemma fold_mupinv u A : (A^T *m A + u *ml: I)^^-1 *m A^T = A^-u.
Proof. by rewrite unlock. Qed.

Lemma fold_mupinvT u A : A *m (A^T *m A + u *ml: I)^^-1 = (A^-u)^T.
Proof. 
  set goal := LHS.
  by rewrite unlock trmx_mul trmxK trmx_inv linearD /= trmx_mul trmxK trmx_lscalemx trmx1.
Qed.

End MuPseudoinverse.

Local Notation "A ^- u" := (mupinv u A) : ring_scope.

Section Appendix.

(* Scalar type *)
Variable R : ringType.
(* Element type *)
Variable E : unitComAlgType R.
Variable D : comBimodType E.
Variable der : {linearDer E -> D}.
Notation "\d" := (LinearDer.apply der).
Notation "\\d" := (map_mx \d).

Variable m n' : nat.
Local Notation n := n'.+1.
Implicit Types A : 'M[E]_(m, n).
Implicit Types B : 'M[E]_n.

Variable A : 'M[E]_(m, n).
Variable u : R.

Hypothesis h_invertible : invertible (mupinv_core u A).

Lemma AmupinvA_sym : (A *m A^-u)^T = A *m A^-u.
Proof. by rewrite trmx_mul -fold_mupinvT -fold_mupinv mulmxA. Qed.

(* The 'suff' tactic is for explicitly expressing the desired immediate results of each step. If the immediate results are not interesting, the 'suff' tactic can be removed and only rewrites are needed *)
Lemma dm_mupinv : \\d (A^-u) = 0 - A^-u *ml \\d A *mr A^-u + (A^T *m A + u *ml: I)^-1 *ml (\\d A)^T *mr (I - A *m A^-u).
Proof.
  set goal := RHS.

  suff ?: \\d (A^T *m A + u *ml: I) ^^-1 *mr A^T + (A^T *m A + u *ml: I) ^^-1 *ml \\d A^T = goal 
  by rewrite unlock dmM /mupinv_core /=.

  suff ?: 0 - ((A^T *m A + u *ml: I) ^^-1 *ml \\d (A^T *m A + u *ml: I)) *mr (A^T *m A + u *ml: I) ^^-1 *mr A^T + (A^T *m A + u *ml: I) ^^-1 *ml \\d A^T = goal
  by rewrite !invmx_inv (derV _ h_invertible) /mupinv_core -!invmx_inv /= rmulNmx -sub0r.

  suff ?: 0 - (A^T *m A + u *ml: I) ^^-1 *ml (\\d A^T *mr A + A^T *ml \\d A) *mr (A^T *m A + u *ml: I) ^^-1 *mr A^T + (A^T *m A + u *ml: I) ^^-1 *ml \\d A^T = goal
  by rewrite raddfD /= dmcs dmI lscalemx0 addr0 dmM /=.

  suff ?: 0 - (A^T *m A + u *ml: I) ^^-1 *ml \\d A^T *mr A *mr A ^- u - ((A^T *m A + u *ml: I) ^^-1 *m A^T) *ml \\d A *mr A ^- u + (A^T *m A + u *ml: I) ^^-1 *ml \\d A^T = goal             
  by rewrite -rmulmxA fold_mupinv lmulmxDr rmulmxDl lrmulmxA lmulmxA opprD addrA.

  by rewrite fold_mupinv sub0r [in - _ - _]addrC -addrA [in - _ + (_ *ml \\d _)](addrC) -rmulmxA -rmulmx1Br -map_trmx -sub0r.
Qed.

Lemma dm_AmupinvA : \\d (A *m A^-u) = sym ((I - A *m A^-u) *ml \\d A *mr A^-u).
Proof.
  set goal := RHS.

  suff ?: \\d A *mr A ^- u + A *ml \\d (A ^- u) = goal
  by rewrite dmM /=.

  suff ?: \\d A *mr A ^- u - (A *m A ^- u) *ml \\d A *mr A ^- u + (A *m (A^T *m A + u *ml: I)^-1) *ml (\\d A)^T *mr (I - A *m A ^- u) = goal             
  by rewrite dm_mupinv sub0r !(lmulmxDr A) lmulmxN !addrA !lrmulmxA !lmulmxA.

  suff ?: \\d A *mr A ^- u - (A *m A ^- u) *ml \\d A *mr A ^- u + (A ^- u)^T *ml (\\d A)^T *mr (I - A *m A ^- u) = goal
  by rewrite fold_mupinvT.

  suff ?: \\d A *mr A ^- u - (A *m A ^- u) *ml \\d A *mr A ^- u + (A ^- u)^T *ml (\\d A)^T - (A ^- u)^T *ml (\\d A)^T *mr A *mr A ^- u = goal
  by rewrite !rmulmxDr rmulmx1 rmulmxN !rmulmxA !addrA.

  suff ?: sym (\\d A *mr A ^- u - (A *m A ^- u) *ml \\d A *mr A ^- u) = goal
  by rewrite -trmx_rmulmx -rmulmxA -[in _ *mr (A *m _) ]AmupinvA_sym -trmx_lmulmx -addrA -raddfB /= lrmulmxA addrC fold_sym.

  by rewrite -lrmulmxA /= -(lmulmx1Br (A *m _)) lrmulmxA.
Qed.

End Appendix.

Module Notations.

Notation "A ^- u" := (mupinv u A) : ring_scope.

End Notations.
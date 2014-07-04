(* (c) Copyright ? *)

(*****************************************************************************
  Verification of formula deductions in paper "Exact-Wiberg Algorithm for 
  Matrix Factorization with Missing Data" (ECCV 2014 submission)

  Main definitions:
                C : ringType. Type of constants.
                E : unitComAlgType C. Type of variables and matrix elements.
                D : comBimodType E. The co-domain of differentiation operator.
               \d : {linearDer E -> D}. The differentiation operator (derivation)
                    on elements.
              \\d : Matrix differentiation, which is just element-wise 
                    differentiation.
            m n r : non-zero natural numbers
              W M : 'M[E]_(m,n). The weight and target matrix in the matrix 
                    decomposition problem. They are lifted from 'M[C]_(m,n), 
                    so they are constant.
                U : 'M[E]_(m,r)
                v : C
               ~W == diag_mx (vec W)^T
               \m == vec M
               ~U == I *ol U
             eps1 == ~W *m \m - ~W *m ~U *m (~W *m ~U)^-v *m ~W *m \m
                H == I - ~W *m ~U *m (~W *m ~U)^-v
               V* == (cvec_mx ((~W *m ~U)^-v *m ~W *m \m))^T
                R == W .* (M - U *m V*^T)
              ~V* == V* *o I
                T == (trT _ _ _). The permutation matrix for transposing.

  Main results: 
    vec_dot : forall V,
      vec (W .* (M - U *m V^T)) = ~W *m \m - ~W *m ~U *m vec V^T
      Corresponds to Equation (10)~(13)

    d_eps1_part1 : 
      \\d eps1 = 0 - H *m ~W *ml (I *ol \\d U) *mr ((~W *m ~U)^-v *m ~W *m \m) - 
                ((~W *m ~U)^-v)^T *ml (I *ol (\\d U)^T) *mr (~W^T *m H *m ~W *m \m)
      Corresponds to Equation (20)~(26)

    to_vec_dot : 
      ~W^T *m H *m ~W *m \m = vec (W .* R)
      Corresponds to Equation (28)~(31) 

    d_eps1 : 
      \\d eps1 = 0 - (H *m ~W *m ~V* + ((~W *m ~U)^-v)^T *m ((W .* R)^T *o I) *m T)
                 *ml \\d (vec U)
      Corresponds to Equation (32)~(34) 

  All results are under the assumption: invertible (mupinv_core v (~W *m ~U)).
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

Require Import diffalg.
Open Local Scope diff_scope.

Require Import bimodule.
Require Import derivation.
Require Import mxutil.
Import Notations.
Require Import mxmodule.
Import Notations.
Require Import mxdiff2.
Import Notations.
Require Import eccv_paper_appendix2.
Import Notations.

Section Section3.

(* Constants *)
Variable C : ringType.
(* Variables and matrix elements *)
Variable E : unitComAlgType C.
(* Co-domain of differentiation operator *)
Variable D : comBimodType E.
Variable der : {linearDer E -> D}.
Notation "\d" := (LinearDer.apply der).
Notation "\\d" := (map_mx \d).

(* All dimensions are non-zero. All matrices are non-empty. *)
Variable m' n' r' : nat.
Local Notation m := m'.+1.
Local Notation n := n'.+1.
Local Notation r := r'.+1.

(* W : weight matrix 
   M : target matrix 
   They are constant matrices, and are lifted to participate in matrix operations.
*)
Variable cW cM : 'M[C]_(m, n).
Notation W := (lift cW).
Notation M := (lift cM).
Variable U : 'M[E]_(m, r).
Notation "~W" := (diag_mx (vec W)^T).
Notation "\m" := (vec M).
Notation "~U" := (I *o U).

(* The 'suff' tactic is for explicitly expressing the desired immediate results of each step. If the immediate results are not interesting, the 'suff' tactic can be removed and only rewrites are needed *)
(* Corresponds to Equation (10)~(13) *)
Lemma vec_dot V : vec (W .* (M - U *m V^T)) = ~W *m \m - ~W *m ~U *m vec V^T.
Proof.
  set goal := RHS.

  suff ?: ~W *m vec (M - U *m V^T) = goal
  by rewrite vec_elemprod.

  suff ?: ~W *m \m - ~W *m vec (U *m V^T) = goal
  by rewrite !raddfB /=.

  by rewrite vec_kron !mulmxA.
Qed.

(* Regularization rate *)
Variable v : C.

Definition eps1 := ~W *m \m - ~W *m ~U *m (~W *m ~U)^-v *m ~W *m \m.
Notation H := (I - ~W *m ~U *m (~W *m ~U)^-v).
Hypothesis h_invertible : invertible (mupinv_core v (~W *m ~U)).

Lemma dmmr {p} (A : 'M[E]_(p, _)) : \\d (A *m \m) = \\d A *mr \m.
Proof.
  by rewrite -!lift_vec !dmcr.
Qed.

Lemma dmWr {p} (A : 'M[E]_(p, _)) : \\d (A *m ~W) = \\d A *mr ~W.
Proof.
  by rewrite -!lift_vec map_trmx -map_diag_mx !dmcr.
Qed.

Lemma dmWl {p} (A : 'M[E]_(_, p)) : \\d (~W *m A) = ~W *ml \\d A.
Proof.
  by rewrite -!lift_vec map_trmx -map_diag_mx !dmcl.
Qed.

(* Corresponds to Equation (20)~(26) *)
Lemma d_eps1_part1 : \\d eps1 = 0 - H *m ~W *ml (I *ol \\d U) *mr ((~W *m ~U)^-v *m ~W *m \m) - ((~W *m ~U)^-v)^T *ml (I *ol (\\d U)^T) *mr (~W^T *m H *m ~W *m \m).
Proof.
  set goal := RHS.

  suff ?: \\d (~W *m \m - ~W *m ~U *m (~W *m ~U) ^- v *m ~W *m \m) = goal
  by rewrite /eps1.

  suff ?: 0 - \\d (~W *m ~U *m (~W *m ~U) ^- v) *mr ~W *mr \m = goal
  by rewrite raddfB /= -(mul1mx (~W *m \m)) !mulmxA !dmmr !dmWr dmI !rmul0mx.

  suff ?: 0 - sym (H *ml \\d (~W *m ~U) *mr (~W *m ~U) ^- v) *mr ~W *mr \m = goal
  by rewrite (dm_AmupinvA _ h_invertible). (* (22) *)

  suff ?: 0 - sym ((H *m ~W) *ml (I *ol map_mx der U) *mr (~W *m ~U) ^- v) *mr ~W *mr \m = goal
  by rewrite dmWl (dm_lkron1mx _ _ U) !lmulmxA. (* (25) *)

  by rewrite /sym [in _^T + _]addrC !trmx_rmulmx !trmx_lmulmx !trmx_mul /= (trmx_lkron I (\\d U)) raddfB /= AmupinvA_sym !trmx1 !rmulmxDl opprD addrA !lrmulmxA !rmulmxA -!rmulmxA !mulmxA.
Qed.

Notation "V*" := ((cvec_mx ((~W *m ~U)^-v *m ~W *m \m))^T).

Lemma to_Vstar : (~W *m ~U)^-v *m ~W *m \m = vec V*^T.
Proof.
  by rewrite (trmxK V*) cvec_mxK.
Qed.

Notation R := (W .* (M - U *m V*^T)).

(* Corresponds to Equation (28)~(31) *)
Lemma to_vec_dot : ~W^T *m H *m ~W *m \m = vec (W .* R).
Proof.
  set goal := RHS.

  suff ?: ~W^T *m ~W *m \m - ~W^T *m ~W *m ~U *m (~W *m ~U) ^- v *m ~W *m \m = goal
  by rewrite mulmxBr !mulmxBl !mulmxA mulmx1.

  suff ?: ~W^T *m ~W *m \m - ~W^T *m ~W *m ~U *m vec V*^T = goal
  by rewrite -(mulmxA _ _ ~W) -(mulmxA _ (_ *m _) \m) to_Vstar.
  
  suff ?: ~W^T *m vec R = goal
  by rewrite -!mulmxA -mulmxBr !mulmxA -vec_dot.

  by rewrite tr_diag_mx -vec_elemprod.
Qed.

Notation "~V*" := (V* *o I).

(* The permutation matrix for transposing *)
Notation T := (trT _ _ _).

(* Corresponds to Equation (32)~(34) *)
Lemma d_eps1 : \\d eps1 = 0 - (H *m ~W *m ~V* + ((~W *m ~U)^-v)^T *m ((W .* R)^T *o I) *m T) *ml \\d (vec U).
Proof.
  set goal := RHS.

  suff ?: 0 - (H *m ~W) *ml (I *ol \\d U) *mr vec V*^T - ((~W *m ~U) ^- v)^T *ml (I *ol (\\d U)^T) *mr vec (W .* R) = goal
  by rewrite d_eps1_part1 to_vec_dot {1}to_Vstar.

  by rewrite -!lrmulmxA !lkron_shift (trmxK V*) !lmulmxA -trTPcrmul !lmulmxA sub0r -opprD -!(lmulmxDl _ _ (vec (\\d U))) -(map_vec _ U) -sub0r.
Qed.

End Section3.


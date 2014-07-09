(* (c) Copyright ? *)

(*****************************************************************************
  Verification of formula deductions in paper "Exact-Wiberg Algorithm for 
  Matrix Factorization with Missing Data" (ECCV 2014 submission)

  Main definitions:
        C :  ringType. Type of constants.
        E :  unitComAlgType C. Type of variables and matrix elements.
        D :  comBimodType E. The co-domain of differentiation operator.
       \d :  {linearDer E -> D}. The differentiation operator (derivation)
             on elements.
      \\d :  Matrix differentiation, which is just element-wise 
             differentiation.
    m n r :  non-zero natural numbers
      W M :  'M[E]_(m,n). The weight and target matrix in the matrix 
             decomposition problem. They are lifted from 'M[C]_(m,n), 
             so they are constant.
        U :  'M[E]_(m,r)
        v :  C
       ~W == diag_mx (vec W)^T
       \m == vec M
       ~U == I *ol U
     eps1 == ~W *m \m - ~W *m ~U *m (~W *m ~U)^-v *m ~W *m \m
        H == I - ~W *m ~U *m (~W *m ~U)^-v
       V* == (cvec_mx ((~W *m ~U)^-v *m ~W *m \m))^T
    R == W .* (M - U *m V*^T)
      ~V* == V* *o I
        T == trT _ _ _. The permutation matrix for transposing.
       v* == (~W *m ~U)^-v *m ~W *m \m
        J == 0 - (~W *m ~U)^-v *m ~W *m (V* *o I) + 
             ((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *m 
             ((W .* R)^T *o I) *m T.
             The Jacobian matrix of v*

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
      \\d eps1 = -(H *m ~W *m ~V* + ((~W *m ~U)^-v)^T *m ((W .* R)^T *o I) *m T) 
                 *ml \\d (vec U)
      Corresponds to Equation (32)~(34) 

    d_vstar_part1 : 
      \\d v* = 0 - (~W *m ~U)^-v *m ~W *ml (I *ol \\d U) *mr 
               ((~W *m ~U)^-v *m ~W *m \m) + 
               ((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *ml 
               (I *ol \\d U)^T *mr (~W^T *m (I - (~W *m ~U) *m (~W *m ~U)^-v) 
               *m ~W *m \m)
      Corresponds to Equation (36)~(40)

    d_vstar_part2 : 
      \\d v* = (0 - (~W *m ~U)^-v *m ~W *m (V* *o I) + ((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *m ((W .* R)^T *o I) *m T) *ml vec (\\d U)
      Corresponds to Equation (40')~(48) 

    J_simpl : 
      J = 0 - ((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *m ((I *o U^T)*m ~W^T *m ~W *m (V* *o I) - ((W .* R)^T *o I) *m T)
      Corresponds to Equation (49)~(52) 

    d_vstar : 
      \\d v* = - (((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *m ((I *o U^T)*m ~W^T *m ~W *m (V* *o I) - ((W .* R)^T *o I) *m T)) *ml \\d (vec U)
      direct corollary from d_vstar_part2 and J_simpl.

  When instantiate the previous results with the following instantiation:
        p == r * m. The number of free variables (which is also the 
             number of elements of U).
        E :  funType p C. Single-value functions on C with up-to p arity.
             The vector of the p free variables are denoted as \x.
       \d :  {gradient E}. A gradient operator on E. This is where
             the Jacobian matrix is defined.
        U == cvec_mx \x. 
             (vec U) is the basis vector of the free variables, with 
             regard to which we want to compute the Jacobian matrices.
       \J == Jacob \d. The Jacobian matrix operator from \d.

  With this instantiation, we then have the following results:
    J_eps1 : 
      \J eps1 = -(H *m ~W *m ~V* + ((~W *m ~U)^-v)^T *m ((W .* R)^T *o I) *m T)

    J_vstar : 
      \J v* = -(((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *m 
              ((I *o U^T)*m ~W^T *m ~W *m (V* *o I) - ((W .* R)^T *o I) *m T))

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

Require Import bimodule.
Require Import derivation.
Require Import mxutil.
Import Notations.
Require Import mxmodule.
Import Notations.
Require Import mxdiff.
Import Notations.
Require Import eccv_paper_appendix.
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

Notation eps1 := (~W *m \m - ~W *m ~U *m (~W *m ~U)^-v *m ~W *m \m).
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

  suff ?: 0 - \\d (~W *m ~U *m (~W *m ~U) ^- v) *mr ~W *mr \m = goal
  by rewrite raddfB /= -(mul1mx (~W *m \m)) !mulmxA !dmmr !dmWr dmI !rmul0mx.

  suff ?: 0 - sym (H *ml \\d (~W *m ~U) *mr (~W *m ~U) ^- v) *mr ~W *mr \m = goal
  by rewrite (dm_AmupinvA _ h_invertible). (* (22) *)

  suff ?: 0 - sym ((H *m ~W) *ml (I *ol \\d U) *mr (~W *m ~U) ^- v) *mr ~W *mr \m = goal
  by rewrite dmWl (dm_lkron1mx _ _ U) !lmulmxA /=. (* (25) *)

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
Lemma d_eps1 : \\d eps1 = -(H *m ~W *m ~V* + ((~W *m ~U)^-v)^T *m ((W .* R)^T *o I) *m T) *ml \\d (vec U).
Proof.
  set goal := RHS.

  suff ?: 0 - (H *m ~W) *ml (I *ol \\d U) *mr vec V*^T - ((~W *m ~U) ^- v)^T *ml (I *ol (\\d U)^T) *mr vec (W .* R) = goal
  by rewrite d_eps1_part1 to_vec_dot {1}to_Vstar.

  by rewrite -!lrmulmxA !lkron_shift (trmxK V*) !lmulmxA -trTPcrmul !lmulmxA sub0r -opprD -!(lmulmxDl _ _ (vec (\\d U))) -(map_vec _ U) -(lmulNmx _ (\\d _)).
Qed.

Notation "v*" := ((~W *m ~U)^-v *m ~W *m \m).

Lemma dmWTr {p} (A : 'M[E]_(p, _)) : \\d (A *m ~W^T) = \\d A *mr ~W^T.
Proof.
  by rewrite -!lift_vec map_trmx -map_diag_mx  map_trmx !dmcr.
Qed.

(* Corresponds to Equation (36)~(40) *)
Lemma d_vstar_part1 : \\d v* = 0 - (~W *m ~U)^-v *m ~W *ml (I *ol \\d U) *mr ((~W *m ~U)^-v *m ~W *m \m) + ((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *ml (I *ol \\d U)^T *mr (~W^T *m (I - (~W *m ~U) *m (~W *m ~U)^-v) *m ~W *m \m).
Proof.
  set goal := RHS.

  suff ?: \\d ((~W *m ~U) ^- v) *mr ~W *mr \m = goal
  by rewrite dmmr dmWr.

  suff ?: 0 - (~W *m ~U) ^- v *ml \\d (~W *m ~U) *mr (~W *m ~U) ^- v *mr ~W *mr \m + ((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^-1 *ml (\\d (~W *m ~U))^T *mr H *mr ~W *mr \m = goal
  by rewrite (dm_mupinv _ h_invertible) 2!rmulmxDl 2!rmulmxBl !rmul0mx.

  by rewrite (map_trmx \d) trmx_mul dmWl dmWTr -(map_trmx \d) !(dm_lkron1mx _ _ U) /= !lrmulmxA !lmulmxA -!rmulmxA !mulmxA -trmx_mul -[in _^T *m _ *m _]mulmxA.
Qed.

(* Corresponds to Equation (40')~(48) *)
Lemma d_vstar_part2 : \\d v* = (0 - (~W *m ~U)^-v *m ~W *m (V* *o I) + ((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *m ((W .* R)^T *o I) *m T) *ml vec (\\d U).
Proof.
  set goal := RHS.

  suff ?: 0 - ((~W *m ~U) ^- v *m ~W) *ml (I *ol \\d U) *mr v* + ((~W *m ~U)^T *m (~W *m ~U) + v *ml: I) ^^-1 *ml (I *ol (\\d U)^T) *mr (~W^T *m H *m ~W *m \m) = goal
  by rewrite d_vstar_part1 trmx_lkron trmx1.

  suff ?: 0 - ((~W *m ~U) ^- v *m ~W) *ml (I *ol \\d U) *mr vec V*^T + ((~W *m ~U)^T *m (~W *m ~U) + v *ml: I) ^^-1 *ml (I *ol (\\d U)^T) *mr vec (W .* R) = goal
  by rewrite to_Vstar to_vec_dot.

  suff ?: 0 - ((~W *m ~U) ^- v *m ~W *m ~V*) *ml vec (\\d U) + (((~W *m ~U)^T *m (~W *m ~U) + v *ml: I) ^^-1 *m ((W .* R)^T *o I)) *ml vec (\\d U)^T = goal
  by rewrite -!lrmulmxA !lkron_shift (trmxK V*) !lmulmxA.

  by rewrite -trTPcrmul !lmulmxA sub0r addrC -!(lmulmxBl _ _ (vec (\\d U))) addrC -sub0r.
Qed.

Notation J := (0 - (~W *m ~U)^-v *m ~W *m (V* *o I) + ((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *m ((W .* R)^T *o I) *m T).

(* Corresponds to Equation (49)~(52) *)
Lemma J_simpl : J = 0 - ((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *m ((I *o U^T)*m ~W^T *m ~W *m (V* *o I) - ((W .* R)^T *o I) *m T).
Proof.
  set goal := RHS.

  suff ?: -(((~W *m ~U)^T *m (~W *m ~U) + v *ml: I) ^^-1 *m ((~W *m ~U)^T *m ~W *m ~V* - (W .* R)^T *o I *m T)) = goal
  by rewrite -{1}fold_mupinv sub0r addrC -opprB -!(mulmxA _^^-1) -mulmxBr.

  by rewrite [in _ - _]trmx_mul [in ~U^T]trmx_kron trmx1 -sub0r.
Qed.

Lemma d_vstar : \\d v* = - (((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *m ((I *o U^T)*m ~W^T *m ~W *m (V* *o I) - ((W .* R)^T *o I) *m T)) *ml \\d (vec U).
Proof.
  set goal := RHS.

  by rewrite d_vstar_part2 J_simpl sub0r -(map_vec _ U).
Qed.

End Section3.

Require Import nfun.

Section Jacobian.

(* All dimensions are non-zero. All matrices are non-empty. *)
Variable m' n' r' : nat.
Notation m := m'.+1.
Notation n := n'.+1.
Notation r := r'.+1.
(* The number of free variables, which is the number of elements of U *)
Notation p := (r * m)%nat.

Variable C : ringType.
Variable E : funType p C.
Variable d : {gradient E}.
Notation "\d" := (Gradient.apply d).
Notation "\\d" := (map_mx \d).

Variable cW cM : 'M[C]_(m, n).
Notation W := (lift cW).
Notation M := (lift cM).
(* (vec U) is the basis vector of the free variables *)
Definition  U : 'M[E]_(m, r) := cvec_mx \x.
Notation "~W" := (diag_mx (vec W)^T).
Notation "\m" := (vec M).
Notation "~U" := (I *o U).
Variable v : C.
Notation eps1 := (~W *m \m - ~W *m ~U *m (~W *m ~U)^-v *m ~W *m \m).
Notation H := (I - ~W *m ~U *m (~W *m ~U)^-v).
Hypothesis h_invertible : invertible (mupinv_core v (~W *m ~U)).
Notation "V*" := ((cvec_mx ((~W *m ~U)^-v *m ~W *m \m))^T).
Notation R := (W .* (M - U *m V*^T)).
Notation "~V*" := (V* *o I).
Notation T := (trT _ _ _).

Notation "\J" := (Jacob \d).

Lemma J_eps1 : \J eps1 = -(H *m ~W *m ~V* + ((~W *m ~U)^-v)^T *m ((W .* R)^T *o I) *m T).
Proof.
  set goal := RHS.

  by rewrite /Jacob (d_eps1 _ _ h_invertible) /= flatten_lmul /= cvec_mxK /= fold_jacob jacob_base mulmx1.
Qed.

Notation "v*" := ((~W *m ~U)^-v *m ~W *m \m).

Lemma J_vstar : \J v* = -(((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *m ((I *o U^T)*m ~W^T *m ~W *m (V* *o I) - ((W .* R)^T *o I) *m T)).
Proof.
  set goal := RHS.

  by rewrite /Jacob (d_vstar _ _ h_invertible) /= flatten_lmul /= cvec_mxK /= fold_jacob jacob_base mulmx1.
Qed.

End Jacobian.
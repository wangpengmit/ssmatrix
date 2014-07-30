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
   They are constant matrices, and are lifted to participate in matrix operations. *)
Variable cW cM : 'M[C]_(m, n).
Notation W := (lift cW).
Notation M := (lift cM).
Variable U : 'M[E]_(m, r).
Notation "~W" := (diag_mx (vec W)^T).
Notation "\m" := (vec M).
Notation "~U" := (I *o U).
(* Regularization rate *)
Variable v : C.
Notation eps1 := (~W *m \m - ~W *m ~U *m (~W *m ~U)^-v *m ~W *m \m).
Notation H := (I - ~W *m ~U *m (~W *m ~U)^-v).
Notation "V*" := ((cvec_mx ((~W *m ~U)^-v *m ~W *m \m))^T).
Notation R := (W .* (M - U *m V*^T)).
Notation "~V*" := (V* *o I).
(* The permutation matrix for transposing *)
Notation T := (trT _ _ _).
Notation "v*" := ((~W *m ~U)^-v *m ~W *m \m).
Notation J2 := (0 - (~W *m ~U)^-v *m ~W *m (V* *o I) + ((~W *m ~U)^T *m (~W *m ~U) + v *ml: I)^^-1 *m ((W .* R)^T *o I) *m T).
Notation J1 := (-(H *m ~W *m ~V* + ((~W *m ~U)^-v)^T *m ((W .* R)^T *o I) *m T)).
Notation "~WR" := ((W .* R) *o I).
Notation "A ^+" := (A^-0) (at level 3, format "A ^+").

Hypothesis h_invertible : invertible (mupinv_core v (~W *m ~U)).

(* Corresponds to Equation (10)~(13) *)
(*! \def\vecDot{ *)
(*! \begin{align} *)
Lemma vec_dot V : vec (W .* (M - U *m V^T)) = ~W *m \m - ~W *m ~U *m vec V^T.
Proof.
  set goal := RHS.
  rewrite vec_elemprod.
  (*! \coqvar{from} &= \coqvar{lhs} *)
  (*!n & \comment{ Define $\tW := \operatorname{diag}(\vec\mW)$ } *)
  rewrite !raddfB /=.
  (*! \\ &= \coqvar{lhs} *)
  (*!n & \xcomment{ Define $\v m := \vec\mM$} \eqlabel{resvec1} *)
  by rewrite vec_kron !mulmxA.
  (*! \\ &= \coqvar{to} \eqlabel{\coqvar{name}} *)
  (*!n & \comment{ Define $\twiddle\mU := \kron{\Id n}{\mU}$} *)
Qed.
(*! \end{align} *)
(*! } *)
(*
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
  rewrite raddfB /= -(mul1mx (~W *m \m)) !mulmxA !dmmr !dmWr dmI !rmul0mx.
  rewrite (dm_AmupinvA _ h_invertible). (* (22) *)
  rewrite dmWl (dm_lkron1mx _ _ U) !lmulmxA /=. (* (25) *)
  by rewrite /sym [in _^T + _]addrC !trmx_rmulmx !trmx_lmulmx !trmx_mul /= (trmx_lkron I (\\d U)) raddfB /= AmupinvA_sym !trmx1 !rmulmxDl opprD addrA !lrmulmxA !rmulmxA -!rmulmxA !mulmxA.
Qed.
*)
Lemma to_Vstar : (~W *m ~U)^-v *m ~W *m \m = vec V*^T.
Proof.
  by rewrite (trmxK V*) cvec_mxK.
Qed.

(* Corresponds to Equation (28)~(31) *)
(*! \def\toVecDot{ *)
(*! \begin{align} *)
Lemma to_vec_dot : ~W^T *m H *m ~W *m \m = vec (W .* R).
Proof.
  set goal := RHS.
  rewrite mulmxBr !mulmxBl !mulmxA mulmx1.
  (*! \coqvar{from} &= \coqvar{lhs} *)
  rewrite -(mulmxA _ _ ~W) -(mulmxA _ (_ *m _) \m) to_Vstar.
  (*! \\ &= \coqvar{lhs} *)
  rewrite -!mulmxA -mulmxBr !mulmxA -vec_dot.
  (*! \\ &= \coqvar{lhs} *)
  by rewrite tr_diag_mx -vec_elemprod.
  (*! \\ &= \coqvar{to} \eqlabel{\coqvar{name}} *)
  (*!n & \comment{ Some comments} *)
Qed.
(*! \end{align} *)
(*! } *)

End Section3.

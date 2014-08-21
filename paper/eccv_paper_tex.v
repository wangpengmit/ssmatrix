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
(* The paper now always assumes v=0 *)
(* Variable v : C. *)
Notation v := 0 (only parsing).
Notation eps1 := (~W *m \m - ~W *m ~U *m (~W *m ~U)^-v *m ~W *m \m).
Notation H := (I - ~W *m ~U *m (~W *m ~U)^-v).
Notation "V*" := ((cvec_mx ((~W *m ~U)^-v *m ~W *m \m))^T).
Notation R := (W .* (M - U *m V*^T)).
Notation "~V*" := (V* *o I).
(* The permutation matrix for transposing *)
Notation T := (trT _ _ _).
Notation "A ^+" := (A^-0) (at level 3, format "A ^+").
(* This notation works better with Latex *)
Notation "{( A )^+}" := (A^-0) (at level 3).

Hypothesis h_invertible : invertible (mupinv_core v (~W *m ~U)).

(* Corresponds to Equation (10)~(13) *)
(*! \def\vecDot{ *)
(*! \begin{align} *)
Lemma vec_dot V : vec (W .* (M - U *m V^T)) = ~W *m \m - ~W *m ~U *m vec V^T.
Proof.
  set goal := RHS.
  rewrite vec_elemprod.
  (*! \coqVar{from} &= \coqVar{lhs} *)
  (*!n & \comment{ Define $\tW := \operatorname{diag}(\vec\mW)$ } *)
  rewrite !raddfB /=.
  (*! \\ &= \coqVar{lhs} *)
  (*!n & \xcomment{ Define $\v m := \vec\mM$} \eqlabel{resvec1} *)
  by rewrite vec_kron !mulmxA.
  (*! \\ &= \coqVar{to} *)
  (*!n & \comment{ Define $\twiddle\mU := \kron{\Id n}{\mU}$} \eqlabel{resvec2} *)
Qed.
(*! \end{align} *)
(*! } *)

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

(* To work with the paper's notation and color scheme *)
Notation "\\d [ A ]" := (\\d A) (format "\\d [ A ]").

(* Corresponds to Equation (20)~(26) *)
(*! \def\dEpsOnePartOne{ *)
(*! \begin{align} *)
Lemma d_eps1_part1 : \\d[eps1] = 0 - H *m ~W *ml (I *ol \\d[U]) *mr ((~W *m ~U)^-v *m ~W *m \m) - ((~W *m ~U)^-v)^T *ml (I *ol (\\d[U])^T) *mr (~W^T *m H *m ~W *m \m).
Proof.
  set goal := RHS.
  rewrite raddfB /= -(mul1mx (~W *m \m)) !mulmxA !dmmr !dmWr dmI !rmul0mx.
  (*! \coqVar{from} &= \coqVar{lhs} *)
  (*!n & \kern-1in\comment{Sum/product rule, and $\partial[\tW\v m] = 0$} *)
  rewrite (dm_AmupinvA _ h_invertible). (* (22) *)
  (*! \\ &= \coqVar{lhs} *)
  (*!n & \comment{From \eqref{diffpinv}} *)
  rewrite dmWl (dm_lkron1mx _ _ U) !lmulmxA /=. (* (25) *)
  (*! \\ &= \coqVar{lhs} *)
  (*!n & \comment{Using \cite[(7)]{minka00}} *)
  (*!n \\ & & \comment{Defining $\m H$, note $\m H=\m H\tr$} *)
  by rewrite /sym [in _^T + _]addrC !trmx_rmulmx !trmx_lmulmx !trmx_mul /= (trmx_lkron I (\\d U)) raddfB /= AmupinvA_sym !trmx1 !rmulmxDl opprD addrA !lrmulmxA !rmulmxA -!rmulmxA !mulmxA.
  (*! \coqLocalSub/\)\s*-/)\\ & \phantom{{}=00} -/ \\ &= \coqVar{to} *)
  (*!n & \comment{Expand $\sym$} *)
  (*! \eqlabel{Jbrackets} *)
Qed.
(*! \end{align} *)
(*! } *)

Lemma to_Vstar : (~W *m ~U)^-v *m ~W *m \m = vec V*^T.
Proof.
  by rewrite (trmxK V* ) cvec_mxK.
Qed.

(* Corresponds to Equation (28)~(31) *)
(*! \def\toVecDot{ *)
(*! \begin{align} *)
Lemma to_vec_dot : ~W^T *m H *m ~W *m \m = vec (W .* R).
Proof.
  set goal := RHS.
  rewrite mulmxBr !mulmxBl !mulmxA mulmx1.
  (*! \coqVar{from} &= \coqVar{lhs} *)
  (*!n & \comment{Expand \m H} *)
  rewrite -(mulmxA _ _ ~W) -(mulmxA _ (_ *m _) \m) to_Vstar.
  (*! \\ &= \coqVar{lhs} *)
  (*!n & \comment{Substitute $\Vstar$} *)
  rewrite -!mulmxA -mulmxBr !mulmxA -vec_dot.
  (*! \\ &= \coqVar{lhs} *)
  (*!n & \comment{Reversing \eqref{erru}} *)
  (*!n \\ & & \comment{Defining $\m R := \mW\hadamard(\mM - \mU \Vstar\tr)$} *)
  by rewrite tr_diag_mx -vec_elemprod.
  (*! \\ &= \coqVar{to} \eqlabel{\coqVar{name}} *)
Qed.
(*! \end{align} *)
(*! } *)

(* Corresponds to Equation (32)~(34) *)
(*! \def\dEpsOne{ *)
(*! \begin{align} *)
Lemma d_eps1 : \\d[eps1] = -(H *m ~W *m ~V* + ((~W *m ~U)^-v)^T *m ((W .* R)^T *o I) *m T) *ml \\d[vec U].
Proof.
  set goal := RHS.
  rewrite d_eps1_part1 to_vec_dot {1}to_Vstar.
  (*! \coqVar{from} &= \coqVar{lhs} *)
  by rewrite -!lrmulmxA !lkron_shift (trmxK V* )!lmulmxA -trTPcrmul !lmulmxA sub0r -opprD -!(lmulmxDl _ _ (vec (\\d U))) -(map_vec _ U) -(lmulNmx _ (\\d _)).
  (*! \\ &= \coqVar{to} *)
  (*!n & \xcomment{By \eqref{kronvec}} *)
  (*!n \\ & & \kern-2cm\comment{Defining $\tVstar:=\kron{\Vstar}{\Id m}$} *)
  (*!n \eqlabel{jacobian} *)
Qed.
(*! \end{align} *)
(*! } *)

Notation J1 := (-(H *m ~W *m ~V* + ((~W *m ~U)^-v)^T *m ((W .* R)^T *o I) *m T)).
Notation "~WR" := ((W .* R) *o I).

Lemma mulpinvmx m n (A : 'M[E]_(m,n)) : invertible (mupinv_core 0 A) -> A^+ *m A = I.
Proof.
  rewrite unlock /mupinv /mupinv_core lscale0mx addr0.
  by move => h; rewrite -(mulmxA _^^-1) mulVmx.
Qed.

Lemma pinv_pinv m n (A : 'M[E]_(m,n)) : invertible (mupinv_core 0 A) -> A^+ *m A^+^T = (A^T *m A)^^-1.
Proof.
  move => h.
  by rewrite [in _^+^T]unlock /mupinv /mupinv_core /= lscale0mx addr0 !trmx_mul !trmxK !mulmxA (mulpinvmx h) mul1mx trmx_inv !trmx_mul !trmxK.
Qed.

Lemma pinvWU_WU : (~W *m ~U)^+ *m ~W *m ~U = I.
Proof.
  move: h_invertible => h.
  by rewrite -mulmxA (mulpinvmx h).
Qed.

Lemma WU_H_0 : (~W *m ~U)^+ *m H = 0.
Proof.
  by rewrite mulmxBr mulmx1 !mulmxA pinvWU_WU mul1mx addrN.
Qed.

Lemma trmx_kronmx1 (R : comRingType) m1 n1 m2 (A : 'M[R]_(m1,n1)) : (A *o I)^T = A^T *o (I : 'M_m2).
Proof. by rewrite trmx_kron trmx1. Qed.

Lemma J1_simpl : J1 = -(H *m ~W *m ~V* + ((~W *m ~U)^+)^T *m ~WR^T *m T).
Proof.
  set goal := RHS.
  by rewrite -[in (W .* R)^T *o _]trmx_kronmx1.
Qed.

Lemma H_H : H^T *m H = H.
Proof.
  by rewrite !raddfB /= AmupinvA_sym !trmx1 mulmx1 mulmxBl mul1mx -!mulmxA ![in _^-v *m _]mulmxA pinvWU_WU !mulmxA !mulmx1 addrN subr0.
Qed.

Lemma pinvWU_pinvWU : (~W *m ~U)^+ *m (~W *m ~U)^+^T = ((~W *m ~U)^T *m (~W *m ~U))^^-1.
Proof.
  move: h_invertible => h.
  by rewrite (pinv_pinv h).
Qed.

(* This notation works better with Latex *)
Notation "{( A )^+}" := (A^-0) (at level 3).

(* Corresponds to Equation (54)~(56) *)
(*! \def\JOneJOne{ *)
(*! \begin{align} *)
Lemma J1_J1 : J1^T *m J1 = ~V*^T *m ~W^T *m H *m ~W *m ~V* + T^T *m ~WR *m ((~W *m ~U)^T *m (~W *m ~U))^^-1 *m ~WR^T *m T.
Proof.
  set goal := RHS.
  rewrite J1_simpl [in _^T] raddfN /= mulNmx mulmxN opprK [in _^T] raddfD /= !trmx_mul (trmxK ~WR) (trmxK _^+) [_ *m (_ + _)]mulmxDl mulmxDr mulmxDr !mulmxA !addrA.
  (*! \coqVar{from} &= *)
  (*! \coqLocalSub/\\Ttrans\s*\+/\Ttrans \\ & \phantom{{}=00} +/ \coqVar{lhs} *)
  (*!n & \comment{Using \eqref{jacobian}} *)
  rewrite -!(mulmxA _ _ H) WU_H_0 -!(mulmxA _ _ _^+^T) -[H^T *m _^+^T]trmx_mul WU_H_0 !mulmxA trmx0 !mulmx0 !mul0mx !addr0.
  (*! \\ &= \coqVar{lhs} *)
  (*!n & \begin{comment} *)
  (*!n Noting\textrm{ }(\tW \tU)^\dagger \m H = \m 0 *)
  (*!n \end{comment} *)
  by rewrite -!(mulmxA _ _ H) H_H -(mulmxA _ _ _^+^T) pinvWU_pinvWU.
  (*! \\ &= \coqVar{to} *)
  (*!n & \begin{comment} *)
  (*!n Noting\textrm{ } \m H^2 = \m H *)
  (*!n \end{comment} *)
  (*!n \eqlabel{jtj} *)
Qed.
(*! \end{align} *)
(*! } *)

(* Corresponds to Equation (57)~(58) *)
(*! \def\JOneEpsOne{ *)
(*! \begin{align} *)
Lemma J1_eps1 : -J1^T *m eps1 = ~V*^T *m ~W^T *m H *m ~W *m \m.
Proof.
  set goal := RHS.
  rewrite -mulmxBl -mulmx1Bl J1_simpl raddfN /= opprK raddfD /= !trmx_mul (trmxK ~WR) (trmxK _^+) !mulmxA !mulmxDl.
  (*! \coqVar{from} &= \coqVar{lhs} *)
  (*!n & \begin{comment}
    Noting\textrm{ }\verru = \m H \tW \v m
    \end{comment} *)
  by rewrite -!(mulmxA _ _ H) H_H -!(mulmxA _ _ H) WU_H_0 !mulmx0 !mul0mx !addr0 !mulmxA.
  (*! \\ &= \coqVar{to} *)
  (*!n & \begin{comment}
    Noting\textrm{ } \m H^\top \m H = \m H\textrm{, }(\tW \tU)^\dagger \m H = \m 0
    \end{comment}
    \eqlabel{-jtf} *)
Qed.
(*! \end{align} *)
(*! } *)

Variable V : 'M[E]_(n, r).
Notation eps1_UV := (vec (W .* (M - U *m V^T))).

(* Corresponds to Equation (60)~(62) *)
(*! \def\dEpsOneUV{ *)
(*! \begin{align} *)
Lemma d_eps1_UV : \\d[eps1_UV] = 0 - ~W *m ~U *ml \\d[vec V^T] - ~W *m (V *o I) *ml \\d[vec U].
Proof.
  set goal := RHS.
  rewrite vec_elemprod !raddfB /= -(mul1mx (~W *m \m)) !mulmxA !dmmr !dmWr dmI !rmul0mx dmWl.
  (*! \coqVar{from} &= \coqVar{lhs} *)
  (*!n & \comment{ From \eqref{resvec1} } *)
  by rewrite vec_kron dmM /= (dm_lkron1mx _ _ U) /= lkron_shift [in _ *o _](trmxK V) -(map_vec _ U) lmulmxDr !lmulmxA [in _ *ml _ + _]addrC opprD addrA.
  (*! \\ &= \coqVar{to} *)
  (*!n & \comment{From \eqref{resvec2}} *)
  (*!n \\ & & \comment{Using \eqref{kronvec}} *)
Qed.
(*! \end{align} *)
(*! } *)

End Section3.

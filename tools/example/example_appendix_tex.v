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

Lemma fold_pinv A : (A^T *m A)^^-1 *m A^T = A^-0.
Proof. 
  by rewrite -(addr0 (_ *m A)) -[in _ + _](lscale0mx I) fold_mupinv.
Qed.

Lemma fold_mupinvT u A : A *m (A^T *m A + u *ml: I)^^-1 = (A^-u)^T.
Proof. 
  set goal := LHS.
  by rewrite unlock trmx_mul trmxK trmx_inv linearD /= trmx_mul trmxK trmx_lscalemx trmx1.
Qed.

Lemma fold_pinvT A : A *m (A^T *m A)^^-1 = (A^-0)^T.
Proof. 
  by rewrite -(addr0 (_ *m A)) -[in _ + _](lscale0mx I) fold_mupinvT.
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
(* The paper now always assumes u=0 *)
(* Variable u : R. *)
Notation u := 0 (only parsing).
Notation "A ^+" := (A^-0) (at level 3, format "A ^+").
(* This notation works better with Latex *)
Notation "{ A ^+}" := (A^-0) (at level 3).
(* To work with the paper's notation and color scheme *)
Notation "\\d [ A ]" := (\\d A) (format "\\d [ A ]").

Hypothesis h_invertible : invertible (A^T *m A).

Lemma AmupinvA_sym : (A *m A^-u)^T = A *m A^-u.
Proof. by rewrite trmx_mul -fold_mupinvT -fold_mupinv mulmxA. Qed.

(*! \def\dmMupinv{ *)
(*! \begin{align*} *)
Lemma dm_mupinv : \\d[A^+] = 0 - A^+ *ml \\d[A] *mr A^+ + (A^T *m A)^-1 *ml (\\d[A])^T *mr (I - A *m A^+).
Proof.
  set goal := RHS.
  rewrite unlock dmM /mupinv_core /= lscale0mx addr0.
  (*! \coqVar{from} &= \coqVar{lhs} *)
  rewrite !invmx_inv (derV _ h_invertible) /mupinv_core -!invmx_inv /= rmulNmx -sub0r scale_lmul rscale_rmul.
  (*! \\ &= \coqVar{lhs} *)
  rewrite dmM /=.
  (*! \\ &= \coqVar{lhs} *)
  rewrite -rmulmxA fold_pinv.
  rewrite lmulmxDr rmulmxDl lrmulmxA lmulmxA opprD addrA.
  (*! \\ &= \coqVar{lhs} *)
  by rewrite fold_pinv sub0r [in - _ - _]addrC -addrA [in - _ + (_ *ml \\d _)](addrC) -rmulmxA -rmulmx1Br -map_trmx -sub0r.
  (*! \\ &= \coqVar{to} *)
  (*!n \eqlabel{diffpinv} *)
Qed.
(*! \end{align*} *)
(*! } *)

(*! \def\dmAmupinvA{ *)
(*! \begin{align} *)
Lemma dm_AmupinvA : \\d[A *m A^+] = sym ((I - A *m A^+) *ml \\d[A] *mr A^+).
Proof.
  set goal := RHS.
  rewrite dmM /=.
  (*! \coqVar{from} &= \coqVar{lhs} *)
  rewrite dm_mupinv sub0r !(lmulmxDr A) lmulmxN !addrA !lrmulmxA !lmulmxA.
  (*! \\ &= \coqVar{lhs} *)
  rewrite fold_pinvT.
  (*! \\ &= \coqVar{lhs} *)
  rewrite !rmulmxDr rmulmx1 rmulmxN !rmulmxA !addrA.
  (*! \\ &= \coqVar{lhs} *)
  rewrite -trmx_rmulmx -rmulmxA -[in _ *mr (A *m _) ]AmupinvA_sym -trmx_lmulmx -addrA -raddfB /= lrmulmxA addrC fold_sym.
  (*! \\ &= \coqVar{lhs} *)
  by rewrite -lrmulmxA /= -(lmulmx1Br (A *m _)) lrmulmxA.
  (*! \\ &= \coqVar{to} *)
Qed.
(*! \end{align} *)
(*! } *)

End Appendix.

Module Notations.

Notation "A ^- u" := (mupinv u A) : ring_scope.

End Notations.
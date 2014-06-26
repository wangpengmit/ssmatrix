(* (c) Copyright ? *)

(*****************************************************************************
  Jacobian matrix
******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice fintype.
Require Import finfun bigop prime binomial.
Require Import zmodp.

Require Import matrix.
Require Import ssralg.
Import GRing.Theory.
Open Local Scope ring_scope.

Require Import diffalg.
Open Local Scope diff_scope.
Require Import mxutil.
Import Notations.
Require Import mxdiff.
Import Notations.

(* Differiential Ring with Argument x where \d x = 1 *)
Module DiffArgRing.
Import GRing.

Section ClassDef.

(* Argument *)
Record mixin_of (R : diffRingType) := Mixin {
  arg : R;
  _ : der arg = 1
}.

Record class_of (T : Type) := Class {
  base : DiffRing.class_of T;
  mixin : mixin_of (DiffRing.Pack base T)
}.

Local Coercion base : class_of >-> DiffRing.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@DiffRing.Pack T b0 T)) :=
  fun bT b & phant_id (DiffRing.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @Ring.Pack cT xclass xT.
Definition diffRingType := @DiffRing.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> DiffRing.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion diffRingType : type >-> DiffRing.type.
Canonical diffRingType.
Notation diffArgRingType := type.
Notation DiffArgRingType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'diffArgRingType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'diffArgRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'diffArgRingType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'diffArgRingType'  'of'  T ]") : form_scope.

Definition arg {R : diffArgRingType} : R := DiffArgRing.arg (DiffArgRing.class R).

Notation "\x" := (@arg _) : diff_scope.

End Exports.

End DiffArgRing.

Import DiffArgRing.Exports.

Section DiffArgRingTheory.

Variables (R : diffArgRingType).

Lemma derx : \d \x = 1 :> R.
Proof. by case: R => ? [] ? []. Qed.

End DiffArgRingTheory.


Lemma dmx {E : diffArgRingType} n : \\d \x%:M = I :> 'M[E]_n.
Proof.
  apply/matrixP => i j; rewrite !mxE.
  case (_ == j).
  - by rewrite derx.
  - by rewrite raddf0.
Qed.


(* Differentiability of scalar-valued functions on vectors *)
Section Differentiable.

  Variable E : diffArgRingType.
  Variable n : nat.
  (* We use column vectors here *)
  Implicit Types f : 'cV[E]_n -> E.

  (* Partial derivative *)
  Definition pd i f := \d (f (\x *: delta_mx i 0)).
  Notation "∂ f / '∂x_' i" := (pd i f) (at level 8, format "∂ f / ∂x_ i") : diff_scope.
  
  (* Differentiability, defined by the chain rule *)
  Definition has_chain_rule f := forall v, \d (f v) = \sum_i pd i f * \d (v i 0).

End Differentiable.

Local Notation "∂ f / '∂x_' i" := (pd i f) (at level 8, format "∂ f / ∂x_ i") : diff_scope.

Section Jacobian.

  Variable E : diffRingType.
  Variable m n : nat.
  Fact jacobian_key : unit. Proof. by []. Qed.
  Variable f : 'cV[E]_m -> 'cV[E]_n.
  Definition jacobian :=
    \matrix[jacobian_key]_(i, j) \\d (f (\x *: delta_mx j 0)) i 0.

  Definition mul_jacob_cV v : jacobian *m \\d v = \\d (f v).
  Proof.
    rewrite /jacobian unlock; apply/cowP => i; rewrite !mxE /=.


rewrite {2}[u]matrix_sum_delta big_ord1 linear_sum; apply/rowP=> i.
by rewrite mxE summxE; apply: eq_bigr => j _; rewrite linearZ !mxE.

  Definition diff_with M := forall v, \\d (f v) = M *m \\d v.


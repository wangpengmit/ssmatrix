(* (c) Copyright ? *)

(*****************************************************************************

******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice fintype.
Require Import finfun bigop prime binomial.
Require Import zmodp.

Require Import ssralg.
Import GRing.Theory.
Open Local Scope ring_scope.
Import GRing.

(* Bimodule *)
Module Bimodule.

Definition axiom (Rl : ringType) (V : lmodType Rl) (Rr : ringType) (m : Lmodule.mixin_of Rr V) := forall a v b, a *: (Lmodule.scale m b v) = Lmodule.scale m b (a *: v).

Section ClassDef.

Variable Rl Rr : ringType.

Record class_of (T : Type) : Type := Class {
  base : Lmodule.class_of Rl T;
  mixin : Lmodule.mixin_of Rr (Zmodule.Pack base T);
  ext : @axiom Rl (Lmodule.Pack _ base T) Rr mixin
}.

Local Coercion base : class_of >-> Lmodule.class_of.
Definition base2 T m := Lmodule.Class (@mixin T m).

Structure type (phRl : phant Rl) (phRr : phant Rr) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (phRl : phant Rl) (phRr : phant Rr) (T : Type) (cT : type phRl phRr).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phRl phRr T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack T b0 m0 (axT : @axiom Rl (@Lmodule.Pack _ _ T b0 T) Rr m0) :=
  fun bT b & phant_id (@Lmodule.class Rl phRl bT) (b : @Lmodule.class_of Rl T) =>
  fun mT m & phant_id (@Lmodule.class Rr phRr mT) (@Lmodule.Class Rr T b m) =>
  fun ax & phant_id axT ax =>
  Pack (Phant Rl) (Phant Rr) (@Class T b m ax) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition lmodType := @Lmodule.Pack Rl phRl cT xclass xT.
Definition rlmodType := @Lmodule.Pack Rr phRr cT (base2 xclass) xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Lmodule.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.
Notation bimodType Rl Rr := (type (Phant Rl) (Phant Rr)).
Notation BimodType Rl Rr T a := (@pack _ _ (Phant Rl) (Phant Rr) T _ _ a _ _ id _ _ id _ id).
Notation "[ 'bimodType' Rl Rr 'of' T 'for' cT ]" := (@clone _ _ (Phant Rl) (Phant Rr) T cT _ idfun)
  (at level 0, format "[ 'bimodType'  Rl Rr  'of'  T  'for'  cT ]")
  : form_scope.
Notation "[ 'bimodType' Rl Rr 'of' T ]" := (@clone _ _ (Phant Rl) (Phant Rr) T _ _ id)
  (at level 0, format "[ 'bimodType'  Rl Rr  'of'  T ]") : form_scope.

Definition rscale (Rl Rr : ringType) (V : bimodType Rl Rr) (v : V) (b : Rr) := b *: (v : rlmodType V).

Notation ":*%R" := (@rscale _ _ _).
Notation "v :* b" := (rscale v b) : ring_scope.

End Exports.

End Bimodule.
Import Bimodule.Exports.

Section BimoduleTheory.

Variables (Rl Rr : ringType) (V : bimodType Rl Rr).
Implicit Types (a : Rl) (b : Rr) (v : V).

Lemma scalerlA a b v : a *: (v :* b) = a *: v :* b.
Proof. 
  by case: V v => ? [] ? [] ? ? ? ? ? ext ? ?; rewrite /= ext.
Qed.

Lemma scaler1 : @right_id V Rr 1 :*%R.
Proof. by move => v; rewrite /rscale scale1r. Qed.

End BimoduleTheory.

Export Bimodule.Exports.
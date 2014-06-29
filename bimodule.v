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

Local Notation "R ^cc" := (converse_ringType R) (at level 2, format "R ^cc") : type_scope.

(* Right module: a right R-module is just a left R^c-module *)
Module Rmodule.

Section ClassDef.

Variable R : ringType.
Definition class_of := (Lmodule.class_of R^cc).

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phR T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : Lmodule.mixin_of R^cc (@Zmodule.Pack T b0 T)) :=
  fun bT b & phant_id (Zmodule.class bT) b =>
  fun    m & phant_id m0 m => Pack phR (@Lmodule.Class R^cc T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition lmodType :=@Lmodule.Pack R^cc (Phant _) cT xclass xT.

End ClassDef.

Module Import Exports.
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
Notation rmodType R := (type (Phant R)).
Notation RmodType R T m := (@pack _ (Phant R) T _ m _ _ id _ id).
Notation "[ 'rmodType' R 'of' T 'for' cT ]" := (@clone _ (Phant R) T cT _ idfun)
  (at level 0, format "[ 'rmodType'  R  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'rmodType' R 'of' T ]" := (@clone _ (Phant R) T _ _ id)
  (at level 0, format "[ 'rmodType'  R  'of'  T ]") : form_scope.
End Exports.

End Rmodule.
Import Rmodule.Exports.

Definition rscale {R : ringType} {V : rmodType R} (v : V) (b : R) : V := (b : _^c) *: v.
Notation ":*%R" := (@rscale _ _).
Notation "v :* b" := (rscale v b) : ring_scope.

Section RmoduleTheory.

Variables (R : ringType) (V : rmodType R).
Implicit Types (v : V).

Lemma scaleAr v a b : v :* (a * b) = v :* a :* b.
Proof.
  by rewrite /rscale scalerA.
Qed.

End RmoduleTheory.

(* Make a Rmodule from properties suitable for right-scale *)
Module MakeRmodule. (* hide the local notations *)
Section MakeRmodule.

Variable R : ringType.
Variable V : zmodType.
Variable scale : V -> R -> V.
Notation "v ::* a" := (scale v a) (at level 40).
Hypothesis assoc : forall v a b, v ::* (a * b) = v ::* a ::* b.
Hypothesis rightid : forall v, v ::* 1 = v.
Hypothesis vdistr : forall v1 v2 a, (v1 + v2) ::* a = v1 ::* a + v2 ::* a.
Hypothesis sdistr : forall v a b, v ::* (a + b) = v ::* a + v ::* b.
Implicit Types a b : R^c.
Let scale' := (fun (a : R^c) v => v ::* a).
Notation "a *:: v" := (scale' a v) (at level 40).
Lemma assoc' a b v : a *:: (b *:: v) = (a * b) *:: v.
Proof. by subst scale'; simpl; rewrite assoc. Qed.

Lemma leftid : left_id 1 scale'.
Proof. by move => v; subst scale'; simpl; rewrite rightid. Qed.

Lemma rdist : right_distributive scale' +%R.
Proof. by move => a v1 v2; subst scale'; simpl; rewrite vdistr. Qed.

Lemma ldist v a b : (a + b) *:: v = a *:: v + b *:: v.
Proof. by subst scale'; simpl; rewrite sdistr. Qed.

Definition mk_mixin := @LmodMixin _ (Zmodule.Pack _ V) _ assoc' leftid rdist ldist.
Definition mk_rmodType := Eval hnf in RmodType _ _ mk_mixin.
Definition mk_c_lmodType := Eval hnf in LmodType _ _ mk_mixin.

End MakeRmodule.
End MakeRmodule.

(* Bimodule : a R-S-bimodule is both a left R-module and a right S-module *)
Module Bimodule.

Section ClassDef.

Variable R S : ringType.

Definition axiom (V : Type) (lscale : R -> V -> V) (rscale : V -> S -> V) := forall a v b, lscale a (rscale v b) = rscale (lscale a v) b.

Record class_of (T : Type) : Type := Class {
  base : Rmodule.class_of S T;
  mixin : Lmodule.mixin_of R (Zmodule.Pack base T);
  ext : @axiom T (Lmodule.scale mixin) (@rscale S (Rmodule.Pack _ base T))
}.

Local Coercion base : class_of >-> Rmodule.class_of.
Definition base2 R m := Lmodule.Class (@mixin R m).
Local Coercion base2 : class_of >-> Lmodule.class_of.

Structure type (phR : phant R) (phS : phant S) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (phS : phant S) (T : Type) (cT : type phR phS).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phR phS T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack T lscale rscale (axT : @axiom T lscale rscale) :=
  fun bT b & phant_id (@Rmodule.class S phS bT) (b : Rmodule.class_of S T) =>
  fun mT m & phant_id (@Lmodule.class R phR mT) (@Lmodule.Class R T b m) =>
  fun ax & phant_id axT ax =>
  Pack (Phant R) (Phant S) (@Class T b m ax) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition to_zmodType := @Zmodule.Pack cT xclass xT.
Definition to_lmodType := @Lmodule.Pack R phR cT xclass xT.
Definition to_rmodType := @Rmodule.Pack S phS cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Rmodule.class_of.
Coercion base2 : class_of >-> Lmodule.class_of.
Coercion sort : type >-> Sortclass.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion to_zmodType : type >-> Zmodule.type.
Canonical to_zmodType.
Coercion to_lmodType : type >-> Lmodule.type.
Canonical to_lmodType.
Coercion to_rmodType : type >-> Rmodule.type.
Canonical to_rmodType.
Notation bimodType R S := (type (Phant R) (Phant S)).
Notation BimodType R S T a := (@pack _ _ (Phant R) (Phant S) T _ _ a _ _ id _ _ id _ id).
Notation "[ 'bimodType' R ',' S 'of' T 'for' cT ]" := (@clone _ _ (Phant R) (Phant S) T cT _ idfun)
  (at level 0, format "[ 'bimodType'  R ',' S  'of'  T  'for'  cT ]")
  : form_scope.
Notation "[ 'bimodType' R ',' S 'of' T ]" := (@clone _ _ (Phant R) (Phant S) T _ _ id)
  (at level 0, format "[ 'bimodType'  R ',' S  'of'  T ]") : form_scope.

End Exports.

End Bimodule.
Import Bimodule.Exports.

Section BimoduleTheory.

Variables (R S : ringType) (V : bimodType R S).
Implicit Types (v : V).

Lemma scalerlA (a : R) v b : a *: (v :* b) = a *: v :* b.
Proof. 
  by case: V v => sort [] base mixin ext T v; rewrite /rscale /scale ext.
Qed.

End BimoduleTheory.

Export Rmodule.Exports.
Export Bimodule.Exports.

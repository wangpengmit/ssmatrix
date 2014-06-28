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
Notation class_of := (Lmodule.class_of R^cc).

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


(* Bimodule : a R-S-bimodule is both a left R-module and a right S-module *)
Module Bimodule.

Section ClassDef.

Variable R S : ringType.
Notation Sc := S^cc.

Definition axiom V (ml : Lmodule.mixin_of R V) (mr : Lmodule.mixin_of Sc V) := forall a v b, Lmodule.scale ml a (Lmodule.scale mr b v) = Lmodule.scale mr b (Lmodule.scale ml a v).

Record class_of (T : Type) : Type := Class {
  base : Lmodule.class_of R T;
  mixin : Lmodule.mixin_of Sc (Zmodule.Pack base T);
  ext : axiom base mixin
}.

Local Coercion base : class_of >-> Lmodule.class_of.
Definition rmod_class T c := Lmodule.Class (@mixin T c).

Structure type (phR : phant R) (phS : phant S) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (phS : phant S) (T : Type) (cT : type phR phS).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack phR phS T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack T (b0 : Lmodule.class_of _ T) m0 (axT : axiom b0 m0) :=
  fun bT b & phant_id (@Lmodule.class R phR bT) (b : @Lmodule.class_of R T) =>
  fun mT m & phant_id (@Lmodule.class Sc (Phant _) mT) (@Lmodule.Class Sc T b m) =>
  fun ax & phant_id axT ax =>
  Pack (Phant R) (Phant S) (@Class T b m ax) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition to_zmodType := @Zmodule.Pack cT xclass xT.
Definition to_lmodType := @Lmodule.Pack R phR cT xclass xT.
Definition to_rmodType := @Rmodule.Pack S phS cT (rmod_class xclass) xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Lmodule.class_of.
Coercion sort : type >-> Sortclass.
Bind Scope ring_scope with sort.
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

Section Repack.

  Variable R : ringType.
  Variable V : zmodType.
  Implicit Types m : Lmodule.mixin_of R V.

  Definition repack m := let: Lmodule.Mixin s sA idl rd a := m in @Lmodule.Mixin R^cc^cc _ s sA idl rd a.

  Lemma repack_scale m : forall a v, Lmodule.scale (repack m) a v = Lmodule.scale m a v.
  Proof. case m; intros; by rewrite /repack /=. Qed.

End Repack.

(* Converse bimodule: an R-S-bimodule is also an S^c-R^c-bimodule *)
Section Converse.

Variable R S : ringType.

Section ClassDef.

Variable T : Type.
Variable c : Bimodule.class_of R S T.

Let rmod_class := Bimodule.rmod_class c.
Let lmod_class := repack (Lmodule.mixin c).

Lemma cmod_axiom : Bimodule.axiom rmod_class lmod_class.
Proof.
  subst rmod_class lmod_class.
  case: c => base mixin ext.
  rewrite /=.
  move => a v b.
  by rewrite !repack_scale.
Qed.

Definition cmod_class := Bimodule.Class cmod_axiom.

End ClassDef.

Section TypeDef.

Variable (phR : phant R) (phS : phant S) (cT : Bimodule.type phR phS).

Let xT := Bimodule.sort cT.
Let xclass := Bimodule.class cT.
Definition cmodType := @Bimodule.Pack S^cc R^cc (Phant _) (Phant _) cT (cmod_class xclass) xT.

End TypeDef.

End Converse.

Definition cmod V : Type := V.
Notation "V ^r" := (cmod V) (at level 2, format "V ^r") : type_scope.

Section Canonicals.

Variable R S : ringType.
Variable V : bimodType R S.

Canonical cmod_eqType := [eqType of V^r].
Canonical cmod_choiceType := [choiceType of V^r].
Canonical cmod_zmodType := [zmodType of V^r].
Canonical cmod_lmodType := [lmodType S^cc of (cmodType V)^r].
Canonical cmod_rmodType := [rmodType R^cc of (cmodType V)^r].
Canonical cmod_bimodType := [bimodType S^cc,R^cc of (cmodType V)^r].

End Canonicals.

Export Rmodule.Exports.
Export Bimodule.Exports.

(* Differential Algebra *)
(* Author: Peng Wang *)
(* Require SSReflect 1.5 and MathComp 1.5 *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice fintype.
Require Import finfun bigop prime binomial.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Import ssralg.
Import GRing.
Import Zmodule.Exports.
Import Ring.Exports.
Import UnitRing.Exports.
Import Lmodule.Exports.
Import Field.Exports.
Import Lalgebra.Exports.
Import Algebra.Exports.
Import Linear.Exports.
Open Scope ring_scope.


(* Differiential Ring *)
Module DiffRing.

Section ClassDef.

(* Derivation *)
Record mixin_of (R : ringType) := Mixin {
  der : R -> R;
  _ : additive der;
  _ : forall a b, der (a * b) = der a * b + a * der b
}.

Record class_of (T : Type) := Class {
  base : Ring.class_of T;
  mixin : mixin_of (Ring.Pack base T)
}.

Local Coercion base : class_of >-> Ring.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of (@Ring.Pack T b0 T)) :=
  fun bT b & phant_id (Ring.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @Ring.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Ring.class_of.
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
Notation diffRingType := type.
Notation DiffRingType T m := (@pack T _ m _ _ id _ id).
Notation "[ 'diffRingType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'diffRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'diffRingType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'diffRingType'  'of'  T ]") : form_scope.

Definition der {R : diffRingType} : R -> R := DiffRing.der (DiffRing.class R).

Delimit Scope diff_scope with diff.

Notation "\d" := (@der _) : diff_scope. 

End Exports.

End DiffRing.

Import DiffRing.Exports.
Open Scope diff_scope.

Section DiffRingTheory.

Variables (R : diffRingType).
Implicit Types (a b : R).

Definition der_prod a b : \d (a * b) = \d a * b + a * \d b.
Proof. 
  by case: R a b => ? [] ? [].
Qed.

Lemma der1 : @der R 1 = 0.
Proof.
  apply: (addIr (\d (1 * 1))).
  rewrite add0r {1}mul1r.
    by rewrite der_prod mulr1 mul1r.
Qed.

End DiffRingTheory.

(* Differiential Unit Ring *)
Module UnitDiffRing.

Section ClassDef.

Record class_of (T : Type) := Class {
  base : UnitRing.class_of T;
  mixin : DiffRing.mixin_of (Ring.Pack base T)
}.

Definition base2 R m := DiffRing.Class (@mixin R m).
Local Coercion base : class_of >-> UnitRing.class_of.
Local Coercion base2 : class_of >-> DiffRing.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun bT b & phant_id (UnitRing.class bT) (b : UnitRing.class_of T) =>
  fun mT m & phant_id (DiffRing.class mT) (@DiffRing.Class T b m) =>
  Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @Ring.Pack cT xclass xT.
Definition diffRingType := @DiffRing.Pack cT xclass xT.
Definition unitRingType := @UnitRing.Pack cT xclass xT.
Definition unit_diffRingType := @DiffRing.Pack unitRingType xclass xT.

End ClassDef.

Module Import Exports.
Coercion base : class_of >-> UnitRing.class_of.
Coercion mixin : class_of >-> DiffRing.mixin_of.
Coercion base2 : class_of >-> DiffRing.class_of.
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
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Canonical unit_diffRingType.
Notation unitDiffRingType := type.
Notation "[ 'unitDiffRingType' 'of' T ]" := (@pack T _ _ id _ _ id)
  (at level 0, format "[ 'unitDiffRingType'  'of'  T ]") : form_scope.
End Exports.

End UnitDiffRing.

Import UnitDiffRing.Exports.

Section Util.

Variable Z : zmodType.
Variable R : ringType.

Implicit Types x y : Z.

Lemma addNRL x y : x + y = 0 -> x = -y.
  move => H.
  rewrite -sub0r.
  rewrite -H.
  rewrite addrK.
  by done.
Qed.

End Util.

Section UnitDiffRingTheory.

Variable R : unitDiffRingType.
Implicit Types x y : R.
Variable x : R.
Hypothesis Hu : x \is a unit.

Lemma der_inv : \d (x^-1) = - x^-1 * \d x / x.
Proof.
  have He: \d (x / x) = 0.
    rewrite mulrV.
      by apply der1.
      by done.
  rewrite der_prod in He.
  rewrite mulNr.
  rewrite mulNr.
  apply addNRL.
  rewrite addrC.
  apply (mulrI Hu).
  rewrite mulr0.
  rewrite mulrDr.
  rewrite mulrA.
  rewrite mulrA.
  rewrite divrr.
    by rewrite mul1r.
    by done.
Qed.

End UnitDiffRingTheory.


(* Differiential Field *)
Module DiffField.

Section ClassDef.

Record mixin_of (A : fieldType) := Mixin {
  mixin_base : DiffRing.mixin_of A
}.

Record class_of (T : Type) := Class {
  base : Field.class_of T;
  mixin : mixin_of (Field.Pack base T)
}.

Local Coercion base : class_of >-> Field.class_of.
Local Coercion mixin_base : mixin_of >-> DiffRing.mixin_of.
Definition base2 R m := DiffRing.Class (@mixin R m).
Local Coercion base2 : class_of >-> DiffRing.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of b0) :=
  fun bT b & phant_id (@Field.class bT) (b : Field.class_of T) =>
  fun  m & phant_id m0 m =>
  Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @Ring.Pack cT xclass xT.
Definition fieldType := @Field.Pack cT xclass xT.
Definition diffRingType := @DiffRing.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Field.class_of.
Coercion base2 : class_of >-> DiffRing.class_of.
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
Coercion fieldType : type >-> Field.type.
Canonical fieldType.
Coercion diffRingType : type >-> DiffRing.type.
Canonical diffRingType.
Notation diffFieldType R := (type (Phant R)).
Notation "[ 'diffFieldType' R 'of' T ]" := (@pack _ (Phant R) T _ _ id _ _ id)
  (at level 0, format "[ 'diffFieldType'  R  'of'  T ]") : form_scope.
End Exports.

End DiffField.

Import DiffField.Exports.


(* Differiential Algebra *)
Module DiffAlgebra.

Section ClassDef.

Variable R : ringType.

Record mixin_of (A : algType R) := Mixin {
  mixin_base : DiffRing.mixin_of A;
  ext : linear (DiffRing.der mixin_base)
}.

Record class_of (T : Type) := Class {
  base : Algebra.class_of R T;
  mixin : mixin_of (Algebra.Pack _ base T)
}.

Local Coercion base : class_of >-> Algebra.class_of.
Local Coercion mixin_base : mixin_of >-> DiffRing.mixin_of.
Definition base2 R m := DiffRing.Class (@mixin R m).
Local Coercion base2 : class_of >-> DiffRing.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack b0 (m0 : mixin_of b0) :=
  fun bT b & phant_id (@Algebra.class R phR bT) (b : Algebra.class_of R T) =>
  fun  m & phant_id m0 m =>
  Pack (Phant R) (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @Ring.Pack cT xclass xT.
Definition lmodType := @Lmodule.Pack R phR cT xclass xT.
Definition lalgType := @Lalgebra.Pack R phR cT xclass xT.
Definition algType := @Algebra.Pack R phR cT xclass xT.
Definition diffRingType := @DiffRing.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> Algebra.class_of.
Coercion base2 : class_of >-> DiffRing.class_of.
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
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.
Coercion lalgType : type >-> Lalgebra.type.
Canonical lalgType.
Coercion algType : type >-> Algebra.type.
Canonical algType.
Coercion diffRingType : type >-> DiffRing.type.
Canonical diffRingType.
Notation diffAlgType R := (type (Phant R)).
Notation "[ 'diffAlgType' R 'of' T ]" := (@pack _ (Phant R) T _ _ id _ _ id)
  (at level 0, format "[ 'diffAlgType'  R  'of'  T ]") : form_scope.
End Exports.

End DiffAlgebra.

Import DiffAlgebra.Exports.


(* Differiential Unit Algebra *)
Module UnitDiffAlgebra.

Section ClassDef.

Variable R : ringType.

Record class_of (T : Type) := Class {
  base : UnitAlgebra.class_of R T;
  mixin : DiffAlgebra.mixin_of (Algebra.Pack _ base T)
}.

Definition base2 R m := DiffAlgebra.Class (@mixin R m).
Local Coercion base : class_of >-> UnitAlgebra.class_of.
Local Coercion base2 : class_of >-> DiffAlgebra.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun bT b & phant_id (@UnitAlgebra.class R phR bT) (b : UnitAlgebra.class_of R T) =>
  fun mT m & phant_id (DiffAlgebra.mixin (@DiffAlgebra.class R phR mT)) m =>
  Pack (Phant R) (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @Ring.Pack cT xclass xT.
Definition unitRingType := @UnitRing.Pack cT xclass xT.
Definition diffRingType := @DiffRing.Pack cT xclass xT.
Definition lmodType := @Lmodule.Pack R phR cT xclass xT.
Definition lalgType := @Lalgebra.Pack R phR cT xclass xT.
Definition algType := @Algebra.Pack R phR cT xclass xT.
Definition unitAlgType := @UnitAlgebra.Pack R phR cT xclass xT.
Definition diffAlgType := @DiffAlgebra.Pack R phR cT xclass xT.
Definition lmod_unitRingType := @Lmodule.Pack R phR unitRingType xclass xT.
Definition lalg_unitRingType := @Lalgebra.Pack R phR unitRingType xclass xT.
Definition alg_unitRingType := @Algebra.Pack R phR unitRingType xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> UnitAlgebra.class_of.
Coercion base2 : class_of >-> DiffAlgebra.class_of.
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
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Coercion diffRingType : type >-> DiffRing.type.
Canonical diffRingType.
Coercion lmodType : type >-> Lmodule.type.
Canonical lmodType.
Coercion lalgType : type >-> Lalgebra.type.
Canonical lalgType.
Coercion algType : type >-> Algebra.type.
Canonical algType.
Coercion unitAlgType : type >-> UnitAlgebra.type.
Canonical unitAlgType.
Coercion diffAlgType : type >-> DiffAlgebra.type.
Canonical diffAlgType.
Canonical lmod_unitRingType.
Canonical lalg_unitRingType.
Canonical alg_unitRingType.

Notation unitDiffAlgType R := (type (Phant R)).
Notation "[ 'unitDiffAlgType' R 'of' T ]" := (@pack _ (Phant R) T _ _ id _ _ id)
  (at level 0, format "[ 'unitDiffAlgType'  R  'of'  T ]") : form_scope.
End Exports.

End UnitDiffAlgebra.

Import UnitDiffAlgebra.Exports.
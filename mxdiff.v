(* Require SSReflect 1.5 and MathComp 1.5 *)

Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq choice fintype.
Require Import finfun bigop prime binomial.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Import ssralg.

Import GRing.
Import Linear.Exports.
Import Algebra.Exports.
Open Scope ring_scope.

Module DiffAlgebra.

Section ClassDef.

(* Scalars. May need to be field. Not sure *)
Variable R : ringType.

Record mixin_of (A : algType R) := Mixin {
  derivation : {linear A -> A};                                       
  _ : forall a b : A, derivation (a * b) = derivation a * b + a * derivation b
}.

Record class_of (T : Type) := Class {
  base : Algebra.class_of _ T;
  mixin : mixin_of (Algebra.Pack _ base T)
}.

Local Coercion base : class_of >-> Algebra.class_of.

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

End ClassDef.

Module Exports.
Coercion base : class_of >-> Algebra.class_of.
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
Notation dalgType R := (type (Phant R)).
Notation "[ 'dalgType' R 'of' T ]" := (@pack _ (Phant R) T _ _ id _ _ id)
  (at level 0, format "[ 'dalgType'  R  'of'  T ]") : form_scope.
End Exports.

End DiffAlgebra.

Import DiffAlgebra.Exports.

Definition der {R : ringType} {A : dalgType R} : A -> A := fun a => DiffAlgebra.derivation (DiffAlgebra.class A) a.

Definition der_prod : forall {R : ringType} {A : dalgType R} (a b : A), der (a * b) = der a * b + a * der b.
Proof.
  admit.
Qed.

Section DiffAlgebraTheory.

Variable (R : ringType) (A : dalgType R).

Notation "\d" := (@der R A).

Lemma der1 : \d 1 = 0.
Proof.
  apply: (addIr (\d (1 * 1))).
  rewrite add0r {1}mul1r.
    by rewrite der_prod mulr1 mul1r.
Qed.

End DiffAlgebraTheory.

Module UnitDiffAlgebra.

Section ClassDef.

Variable R : ringType.

Record class_of (T : Type) := Class {
  base : DiffAlgebra.class_of R T;
  mixin : UnitRing.mixin_of (Ring.Pack base T)
}.

Definition base2 R m := UnitRing.Class (@mixin R m).
Local Coercion base : class_of >-> DiffAlgebra.class_of.
Local Coercion base2 : class_of >-> UnitRing.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack :=
  fun bT b & phant_id (@DiffAlgebra.class R phR bT) (b : DiffAlgebra.class_of R T) =>
  fun mT m & phant_id (UnitRing.mixin (UnitRing.class mT)) m =>
  Pack (Phant R) (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @Ring.Pack cT xclass xT.
Definition lmodType := @Lmodule.Pack R phR cT xclass xT.
Definition lalgType := @Lalgebra.Pack R phR cT xclass xT.
Definition algType := @Algebra.Pack R phR cT xclass xT.
Definition dalgType := @DiffAlgebra.Pack R phR cT xclass xT.
Definition unitRingType := @UnitRing.Pack cT xclass xT.
Definition lmod_unitRingType := @Lmodule.Pack R phR unitRingType xclass xT.
Definition lalg_unitRingType := @Lalgebra.Pack R phR unitRingType xclass xT.
Definition alg_unitRingType := @Algebra.Pack R phR unitRingType xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> DiffAlgebra.class_of.
Coercion base2 : class_of >-> UnitRing.class_of.
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
Coercion dalgType : type >-> DiffAlgebra.type.
Canonical dalgType.
Coercion unitRingType : type >-> UnitRing.type.
Canonical unitRingType.
Canonical lmod_unitRingType.
Canonical lalg_unitRingType.
Canonical alg_unitRingType.

Notation udalgType R := (type (Phant R)).
Notation "[ 'udalgType' R 'of' T ]" := (@pack _ (Phant R) T _ _ id _ _ id)
  (at level 0, format "[ 'udalgType'  R  'of'  T ]") : form_scope.
End Exports.

End UnitDiffAlgebra.

Import UnitDiffAlgebra.Exports.

Section UnitDiffAlgebraTheory.

Variable (R : ringType) (A : udalgType R).

Notation "\d" := (@der R A).

Lemma der_inv : forall x : A, x \is a unit -> \d (x^-1) = - x^-1 * \d x * x^-1.
Proof.
  move => x Hu.
  have: \d (x / x) = 0.
    admit.
  move => He.
  rewrite der_prod in He.
  admit.
Qed.

End UnitDiffAlgebraTheory.

Require Import matrix.

Module MxDiff.

(* Coefficient type *)
Variable C : fieldType.
(* Element type *)
Variable E : udalgType C.

Notation "\d" := (@der _ E).

Definition Dm m n (A : 'M[E]_(m, n)) := map_mx \d A.

Section AnyMatrix.

Variable m n r : nat.
Definition Mmn := 'M[E]_(m, n).
Definition Mnr := 'M[E]_(n, r).
Implicit Types A : Mmn.
Implicit Types B : Mnr.

Lemma Dm_product : forall A B, Dm (A *m B) = Dm A *m B + A *m Dm B.
Proof.
  admit.
Qed.

End AnyMatrix.

Section SquareMatrix.

(* Square matrices are unit differential algebras *)

Variable n' : nat.
Local Notation n := n'.+1.

Definition matrix_udalgType :=
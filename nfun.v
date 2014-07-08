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

Require Import matrix.
Require Import mxutil.
Import Notations.
Require Import bimodule.
Require Import derivation.
Require Import mxmodule.
Import Notations.

(* The algebraic structure of (up-to) n-variable functions *)
Module Fun.

Section ClassDef.

(* maximum arity (number of formal variables) of each function *)
Variable n : nat.

Record mixin_of (T : Type) := Mixin {
  (* base variables: x_1, x_2, ..., x_n *)
  arg : 'cV[T]_n;
  (* parallel compose/bind/subst/apply. 
     It is easier to define sequential substitution by parallel substitution, than the other way around. *)
  compose : T -> 'cV[T]_n -> T
}.

(* the underlying ring for constant values *)
Variable R : ringType.

Record class_of T := Class {
  base : UnitComAlgebra.class_of R T; 
  mixin : mixin_of T
}.

Local Coercion base : class_of >-> UnitComAlgebra.class_of.

Structure type (phR : phant R) := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (phR : phant R) (T : Type) (cT : type phR).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack (m0 : mixin_of T) :=
  fun bT b & phant_id (@UnitAlgebra.class R phR bT) b =>
  fun m & phant_id m0 m => Pack (Phant R) (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @Ring.Pack cT xclass xT.
Definition unitRingType := @UnitRing.Pack cT xclass xT.
Definition lmodType := @Lmodule.Pack R phR cT xclass xT.
Definition lalgType := @Lalgebra.Pack R phR cT xclass xT.
Definition algType := @Algebra.Pack R phR cT xclass xT.
Definition unitAlgType := @UnitAlgebra.Pack R phR cT xclass xT.
Definition unitComAlgType := @UnitComAlgebra.Pack R phR cT xclass xT.
Definition lmod_unitRingType := @Lmodule.Pack R phR unitRingType xclass xT.
Definition lalg_unitRingType := @Lalgebra.Pack R phR unitRingType xclass xT.
Definition alg_unitRingType := @Algebra.Pack R phR unitRingType xclass xT.
Definition comRingType := @ComRing.Pack cT xclass xT.
Definition comUnitRingType := @ComUnitRing.Pack cT xclass xT.
End ClassDef.

Module Exports.
Coercion base : class_of >-> UnitComAlgebra.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion class : type >-> class_of.
Coercion unitComAlgType : type >-> UnitComAlgebra.type.
Canonical eqType.
Canonical choiceType.
Canonical zmodType.
Canonical ringType.
Canonical unitRingType.
Canonical lmodType.
Canonical lalgType.
Canonical algType.
Canonical unitAlgType.
Canonical unitComAlgType.
Canonical lmod_unitRingType.
Canonical lalg_unitRingType.
Canonical alg_unitRingType.
Canonical comRingType.
Canonical comUnitRingType.

Notation funType n R := (type n (Phant R)).
Notation FunType n R T a := (@pack n _ (Phant R) T a _ _ id _ id).

End Exports.

End Fun.
Import Fun.Exports.

Definition args n (R : ringType) (E : funType n R) := Fun.arg E.
Notation "\x" := (args _) : ring_scope.
Definition arg n (R : ringType) (E : funType n R) i := args E i 0.
Notation "'x@' i" := (arg _ i) (at level 0, format "'x@' i") : ring_scope.
Definition compose {n} {R : ringType} {E : funType n R} := Fun.compose E.
Notation "f \o v" := (compose f v) : ring_scope.
(* induced composition for a matrix of functions *)
Notation "A \\o v" := (map_mx (compose ^~ v) A) (at level 50).

(* flatten a column vector of row vectors to a matrix *)
Definition flatten T m n (A : 'cV['rV[T]_n]_m) := \matrix_(i,j) A i 0 0 j.

(* Gradient: a derivation operator defined by the partial derivatives *)
Module Gradient.

Section ClassDef.

Variable n : nat.
Variable R : ringType.
(* n-variable functions *)
Variable E : funType n R.

Section Mixin.

(* the gradient/derivation operator *)
Variable d : E -> 'rV[E]_n.
(* the Jacobian matrix of a vector of functions, which is just the gradients stacked together *)
Definition jacob m (v : 'cV[E]_m) := flatten (map_mx d v).

Notation J := jacob.

Record mixin_of := Mixin {
  (* behavior of the derivation on base variables *)
  _ : J \x = I;
  (* behavior of the derivation on composition, which is the "chain rule" *)
  _ : forall f v, d (f \o v) = (d f \\o v) *m J v
}.

End Mixin.

Record class_of d := Class {
  base : linearDer d;
  mixin : mixin_of d
}.

Local Coercion base : class_of >-> LinearDer.class_of.
Local Coercion mixin : class_of >-> mixin_of.
                         
Structure map (phE : phant E) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phE : phant E) (d d2 : E -> 'rV[E]_n) (cF : map phE).
Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.
Definition clone fA of phant_id d2 (apply cF) & phant_id fA class :=
  @Pack phE d fA.

Definition pack (fZ : mixin_of d) :=
   fun (bF : LinearDer.map (Phant (E -> 'rV[E]_n))) fA & phant_id (LinearDer.class bF) fA =>
   Pack phE (Class fA fZ).

Definition to_der := DerMorph class.
Definition to_add := Additive class.
Definition to_derAdd := DerAdd class.
Definition to_linear := Linear class.
Definition to_linearDer := LinearDer class.

End ClassDef.

Module Exports.
Notation gradient d := (class_of d).
Coercion apply : map >-> Funclass.
Coercion class : map >-> class_of.
Coercion base : class_of >-> LinearDer.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion to_linearDer : map >-> LinearDer.map.
Canonical to_der.
Canonical to_add.
Canonical to_linear.
Canonical to_derAdd.
Canonical to_linearDer.
Notation Gradient fA := (Pack (Phant _) fA).
Notation packGradient E fA := (@pack _ _ _ (Phant E) _ fA _ _ id).
Notation "{ 'gradient' E }" := (map (Phant E))
  (at level 0, format "{ 'gradient'  E }") : ring_scope.
Notation "[ 'gradient' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'gradient'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'gradient' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'gradient'  'of'  f ]") : form_scope.

Notation Jacob := jacob.

End Exports.

End Gradient.
Import Gradient.Exports.

Section GradientTheory.

Variables (n : nat) (R : ringType) (E : funType n R) (d : {gradient E}) (m : nat) (u : 'cV[E]_m) (v : 'cV[E]_n).

Notation J := (Jacob d).

(* analogous to the single-variable derivative base rule:
   x' = 1 *)
Lemma jacob_base : J \x = I.
Proof. by case: d => /= dd [] base []. Qed.

Lemma chain f : d (f \o v) = (d f \\o v) *m J v.
Proof. by case: d => /= dd [] base []. Qed.

(* analogous to the single-variable derivative chain rule:
   f(g(x))' = f'(g(x)) * g'(x) or (f \o g)' = (f' \o g) * g' *)
Lemma jacob_chain  : J (u \\o v) = (J u \\o v) *m J v.
Proof.
  apply/matrixP => i j.
  rewrite !mxE chain !mxE.
  apply eq_bigr => k _.
  by rewrite !mxE.
Qed.

End GradientTheory.
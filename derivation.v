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

Require Import bimodule.

(* Derivative *)
Module Derivative.

Section ClassDef.

Variable R : ringType.
Variable V : bimodType R R.

Definition axiom (f : R -> V) := forall a b, f (a * b) = f a :* b + a *: f b.

Structure map (phV : phant V) := Pack {apply; _ : axiom apply}.
Local Coercion apply : map >-> Funclass.

Variables (phV : phant V) (f g : R -> V) (cF : map phV).
Definition class := let: Pack _ c as cF' := cF return axiom cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phV f fA.

End ClassDef.

Module Exports.
Notation derivative f := (axiom f).
Coercion apply : map >-> Funclass.
Notation Derivative fA := (Pack (Phant _) fA).
Notation "{ 'derivative' V }" := (map (Phant V))
  (at level 0, format "{ 'derivative'  V }") : ring_scope.
Notation "[ 'derivative' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'derivative'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'derivative' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'derivative'  'of'  f ]") : form_scope.
End Exports.

End Derivative.
Import Derivative.Exports.

Section DerivativeTheory.

Variable R : ringType.
Variable V : bimodType R R.
Variable f : {derivative V}.

Lemma derM a b : f (a * b) = f a :* b + a *: f b.
Proof. by case f. Qed.

Lemma der1 : f 1 = 0.
Proof.
  by apply: (addIr (f (1 * 1))); rewrite add0r {1}mul1r derM scale1r /rscale scale1r.
Qed.

End DerivativeTheory.

Lemma addNRL {Z : zmodType} (x y : Z) : x + y = 0 -> x = -y.
  move => H.
  rewrite -sub0r.
  rewrite -H.
  rewrite addrK.
  by [].
Qed.

Section Inverse.

Variable R : unitRingType.
Variable V : bimodType R R.
Variable f : {derivative V}.

Lemma derV x : x \is a GRing.unit -> f (x^-1) = - (x^-1 *: f x :* x^-1).
Proof.
  move => Hu.
  have He: x^-1 *: f (x / x) = 0 by rewrite (mulrV Hu) der1 scaler0.
  rewrite derM  scalerDr scalerlA scalerA (mulVr Hu) scale1r addrC in He.
  by apply addNRL.
Qed.

End Inverse.

Import GRing.

(* Derivative and Additive *)
Module DerAdd.

Section ClassDef.

Variable R : ringType.
Variable V : bimodType R R.
Implicit Types f : R -> V.

Record class_of f : Prop := Class {base : derivative f; mixin : additive f}.

Local Coercion base : class_of >-> derivative.
Local Coercion mixin : class_of >-> additive.

Structure map (phV : phant V) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phV : phant V) (f g : R -> V) (cF : map phV).
Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.
Definition clone fA of phant_id g (apply cF) & phant_id fA class :=
  @Pack phV f fA.

Definition to_der := Derivative class.
Definition to_add := Additive class.

End ClassDef.

Module Exports.
Coercion apply : map >-> Funclass.
Coercion class : map >-> class_of.
Coercion base : class_of >-> derivative.
Coercion mixin : class_of >-> additive.
Coercion to_der : map >-> Derivative.map.
Canonical to_der.
Coercion to_add : map >-> Additive.map.
Canonical to_add.
Notation DerAdd fA := (Pack (Phant _) fA).
Notation "{ 'derAdd' V }" := (map (Phant V))
  (at level 0, format "{ 'derAdd'  V }") : ring_scope.
Notation "[ 'derAdd' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'derAdd'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'derAdd' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'derAdd'  'of'  f ]") : form_scope.
End Exports.

End DerAdd.
Import DerAdd.Exports.

Export Derivative.Exports.
Export DerAdd.Exports.
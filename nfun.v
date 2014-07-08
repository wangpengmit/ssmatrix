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

(* Ring of (up-to) n-variable functions *)
Module FunRing.

Section ClassDef.

Variable n : nat.

Record mixin_of (T : Type) := Mixin {
  (* base variables: x_1, x_2, ..., x_n *)
  arg : 'I_n -> T;
  (* parallel compose/bind/subst/apply. 
     It is easier to define sequential substitution by parallel substitution, than the other way around. *)
  compose : T -> 'cV[T]_n -> T
}.

Record class_of T := Class {
  base : ComRing.class_of T; 
  mixin : mixin_of T
}.

Local Coercion base : class_of >-> ComRing.class_of.

Structure type := Pack {sort; _ : class_of sort; _ : Type}.
Local Coercion sort : type >-> Sortclass.
Variable (T : Type) (cT : type).
Definition class := let: Pack _ c _ as cT' := cT return class_of cT' in c.
Definition clone c of phant_id class c := @Pack T c T.
Let xT := let: Pack T _ _ := cT in T.
Notation xclass := (class : class_of xT).

Definition pack (m0 : mixin_of T) :=
  fun bT b & phant_id (Ring.class bT) b =>
  fun    m & phant_id m0 m => Pack (@Class T b m) T.

Definition eqType := @Equality.Pack cT xclass xT.
Definition choiceType := @Choice.Pack cT xclass xT.
Definition zmodType := @Zmodule.Pack cT xclass xT.
Definition ringType := @Ring.Pack cT xclass xT.
Definition comRingType := @ComRing.Pack cT xclass xT.

End ClassDef.

Module Exports.
Coercion base : class_of >-> ComRing.class_of.
Coercion mixin : class_of >-> mixin_of.
Coercion sort : type >-> Sortclass.
Coercion class : type >-> class_of.
Coercion eqType : type >-> Equality.type.
Canonical eqType.
Coercion choiceType : type >-> Choice.type.
Canonical choiceType.
Coercion zmodType : type >-> Zmodule.type.
Canonical zmodType.
Coercion ringType : type >-> Ring.type.
Canonical ringType.
Coercion comRingType : type >-> ComRing.type.
Canonical comRingType.
Notation funRingType := type.
Notation FunRingType T m := (@pack T m _ _ id _ id).
Notation FunRingMixin := RingMixin.
Notation "[ 'funRingType' 'of' T 'for' cT ]" := (@clone T cT _ idfun)
  (at level 0, format "[ 'funRingType'  'of'  T  'for'  cT ]") : form_scope.
Notation "[ 'funRingType' 'of' T ]" := (@clone T _ _ id)
  (at level 0, format "[ 'funRingType'  'of'  T ]") : form_scope.

End Exports.

End FunRing.
Import FunRing.Exports.

Definition arg n (E : funRingType n) := FunRing.arg E.
Notation "'x@' i" := (arg _ i) (at level 0, format "'x@' i") : ring_scope.
Definition compose {n} {E : funRingType n} := FunRing.compose E.
Notation "f \o v" := (compose f v) : ring_scope.
(* induced composition for a matrix of functions *)
Notation "A \\o v" := (map_mx (compose ^~ v) A) (at level 50).

(* flatten a column vector of row vectors to a matrix *)
Definition flatten T m n (A : 'cV['rV[T]_n]_m) := \matrix_(i,j) A i 0 0 j.

Require Import bimodule.
Require Import derivation.
Require Import mxmodule.
Import Notations.

(* Gradient: a derivation operator defined by the partial derivatives *)
Module Gradient.

Section ClassDef.

Variable n : nat.
(* ring of n-variable functions *)
Variable E : funRingType n.

(* the gradient/derivation operator *)
Implicit Types d : E -> 'rV[E]_n.
(* the Jacobian matrix of a vector of functions, which is just the gradients stacked together *)
Definition jacob d m (v : 'cV[E]_m) := flatten (map_mx d v).

Notation "\J" := jacob.

Record mixin_of d := Mixin {
  (* behavior of the derivation on base variables *)
  _ : forall i, d x@i = delta_mx 0 i;
  (* behavior of the derivation on composition, which is the "chain rule" *)
  _ : forall f v, d (f \o v) = (d f \\o v) *m \J d v
}.

Record class_of d := Class {
  base : derMorph d;
  mixin : mixin_of d
}.

Local Coercion base : class_of >-> derMorph.
Local Coercion mixin : class_of >-> mixin_of.
                         
Structure map (phE : phant E) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phE : phant E) (d d2 : E -> 'rV[E]_n) (cF : map phE).
Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.
Definition clone fA of phant_id d2 (apply cF) & phant_id fA class :=
  @Pack phE d fA.

Definition pack (fZ : mixin_of d) :=
   fun (bF : DerMorph.map (Phant 'rV[E]_n)) fA & phant_id (DerMorph.class bF) fA =>
   Pack phE (Class fA fZ).

Definition to_der := DerMorph class.

End ClassDef.

Module Exports.
Notation gradient d := (class_of d).
Coercion apply : map >-> Funclass.
Coercion class : map >-> class_of.
Coercion base : class_of >-> derMorph.
Coercion mixin : class_of >-> mixin_of.
Coercion to_der : map >-> DerMorph.map.
Canonical to_der.
Notation Gradient fA := (Pack (Phant _) fA).
Notation packGradient E fA := (@pack _ _ (Phant E) _ fA _ _ id).
Notation "{ 'gradient' E }" := (map (Phant E))
  (at level 0, format "{ 'gradient'  E }") : ring_scope.
Notation "[ 'gradient' 'of' f 'as' g ]" := (@clone _ _ _ f g _ _ idfun id)
  (at level 0, format "[ 'gradient'  'of'  f  'as'  g ]") : form_scope.
Notation "[ 'gradient' 'of' f ]" := (@clone _ _ _ f f _ _ id id)
  (at level 0, format "[ 'gradient'  'of'  f ]") : form_scope.

Notation "\J" := jacob.

End Exports.

End Gradient.
Import Gradient.Exports.

Section GradientTheory.

Variables (n : nat) (E : funRingType n) (d : {gradient E}) (m : nat) (u : 'cV[E]_m) (v : 'cV[E]_n).

Lemma chain f : d (f \o v) = (d f \\o v) *m \J d v.
Proof. by case: d => /= dd [] base []. Qed.

Lemma jacob_chain  : \J d (u \\o v) = (\J d u \\o v) *m \J d v.
Proof.
  apply/matrixP => i j.
  rewrite !mxE chain !mxE.
  apply eq_bigr => k _.
  by rewrite !mxE.
Qed.

End GradientTheory.
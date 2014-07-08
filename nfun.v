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
  (* parallel apply/compose/bind/subst *)
  compose : T -> 'cV[T]_n -> T;
  (* base variables: x_1, x_2, ..., x_n *)
  arg : 'I_n -> T
}.

Record class_of T := Class {
  base : Ring.class_of T; 
  mixin : mixin_of T
}.

Local Coercion base : class_of >-> Ring.class_of.

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

End ClassDef.

Module Exports.
Coercion base : class_of >-> Ring.class_of.
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
Notation "A \\o v" := (map_mx (compose ^~ v) A) (at level 50).

Definition flatten T m n (A : 'cV['rV[T]_n]_m) := \matrix_(i,j) A i 0 0 j.

Require Import bimodule.
Require Import derivation.

(* Derivation operator characterized by the partial derivatives *)
Module FunDer.

Section ClassDef.

Variable n : nat.
(* ring of n-variable functions *)
Variable E : funRingType n.

(* the derivation *)
Implicit Types d : E -> 'rV[E]_n.
(* Jacobian matrix *)
Definition jacob d m (v : 'cV[E]_m) := flatten (map_mx d v).

Notation "\J" := jacob.

Record class_of d := Class {
  (* derivation of base variables *)
  _ : forall i, d x@i = delta_mx 0 i;
  (* chain rule *)
  _ : forall f v, d (f \o v) = (d f \\o v) *m \J d v
}.

Structure map (phE : phant E) := Pack {apply; _ : class_of apply}.
Local Coercion apply : map >-> Funclass.

Variables (phE : phant E) (d : E -> 'rV[E]_n) (cF : map phE).
Definition class := let: Pack _ c as cF' := cF return class_of cF' in c.

End ClassDef.

Module Exports.
Coercion apply : map >-> Funclass.
Coercion class : map >-> class_of.
Notation "{ 'funDer' E }" := (map (Phant E))
  (at level 0, format "{ 'funDer'  E }") : ring_scope.
Notation "\Jacob" := jacob.
End Exports.

End FunDer.
Import FunDer.Exports.

Section FunDerTheory.

Variables (n : nat) (E : funRingType n) (d : {funDer E}) (m : nat) (u : 'cV[E]_m) (v : 'cV[E]_n).
Notation "\J" := (\Jacob d).

Lemma jacob_chain  : \J (u \\o v) = (\J u \\o v) *m \J v.
Proof.
  admit.
Qed.

(* Require SSReflect 1.5 and MathComp 1.5 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Import ssreflect.
Require Import ssralg.
Require Import eqtype seq tuple.
Import ssreflect.SsrSyntax.

Module DiffAlg.
Section DiffAlg.

  Variable F : fieldType.
  (* Element type *)
  Variable E : algType F.
  Import GRing.
  Import Linear.Exports.
  Open Scope ring_scope.
  Definition has_product_rule D := forall a b : E, D (a * b) = D a * b + a * D b.
  (* Derivation *)
  Variable D : {linear E -> E}.
  Hypothesis derD : has_product_rule D.

  Lemma der1 : D 1 = 0.
  Proof.
    apply: (addIr (D (1 * 1))).
    rewrite add0r {1}mul1r.
    by rewrite derD mulr1 mul1r.
  Qed.

End DiffAlg.
End DiffAlg.

Module UnitDiffAlg.
Section UnitDiffAlg.

  Variable F : fieldType.
  (* Element type *)
  Variable E : unitAlgType F.
  Import GRing.
  Import Linear.Exports.
  Open Scope ring_scope.
  Definition has_product_rule D := forall a b : E, D (a * b) = D a * b + a * D b.
  (* Derivation *)
  Variable D : {linear E -> E}.
  Hypothesis derD : has_product_rule D.

  Require Import ssrbool.
  Lemma der_inv : forall x, x \is a unit -> D (x^-1) = - x^-1 * D x * x^-1.
  Proof.
    move => x Hu.
    have: D (x / x) = 0.
      admit.
    move => He.
    rewrite derD in He.
    admit.
  Qed.

End UnitDiffAlg.
End UnitDiffAlg.

Module MxDiffAlg.
Section MxDiffAlg.

  (* Coefficient field *)
  Variable F : fieldType.
  (* Element type *)
  Variable E : unitAlgType F.
  Import GRing.
  Import Linear.Exports.
  Open Scope ring_scope.
  Definition has_product_rule D := forall a b : E, D (a * b) = D a * b + a * D b.
  (* Derivation *)
  Variable D : {linear E -> E}.
  Hypothesis derD : has_product_rule D.

  Require Import matrix.
  Definition Dm m n (A : 'M[E]_(m, n)) := map_mx D A.
  Variable m n r : nat.
  Definition Mmn := 'M[E]_(m, n).
  Definition Mnr := 'M[E]_(n, r).
  Implicit Types A : Mmn.
  Implicit Types B : Mnr.
  Lemma Dm_product : forall A B, Dm (A *m B) = Dm A *m B + A *m Dm B.
  Proof.
    admit.
  Qed.
    
  (* Matrices are algebras *)
  (* Square matrices are unit algebras *)
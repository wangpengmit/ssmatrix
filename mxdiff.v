(* Require SSReflect 1.5 and MathComp 1.5 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Import ssreflect.
Require Import ssralg.
Require Import eqtype seq tuple.
Import ssreflect.SsrSyntax.

Section MxDerivation.

  (* Coefficient field *)
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

  Require Import matrix.
  Definition Dm m n (A : 'M[E]_(m, n)) := map_mx D A.
  Variable m n : nat.
  Definition MXmn := 'M[E]_(m, n).
  Definition MXnm := 'M[E]_(n, m).
  Implicit Types A : MXmn.
  Implicit Types B : MXnm.
  Lemma Dm_product : forall A B, Dm (A *m B) = Dm A *m B + A *m Dm B.
  Proof.
    move => A B.
    
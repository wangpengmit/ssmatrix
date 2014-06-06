(* Require SSReflect 1.5 and MathComp 1.5 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive. 

Require Import ssreflect.
Require Import separable.
Require Import vector.
Require Import fieldext.
Require Import ssralg.
Require Import seq.
Require Import falgebra.
Require Import eqtype.
Require Import tuple.
Import ssreflect.SsrSyntax.

Section MxDerivation.

  Variable F : filedType.
  Variable L : fileExtType F.
  Variable D : 'End(L).
  Hypothesis
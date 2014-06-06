(* Require SSReflect 1.5 and MathComp 1.5 *)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import ssreflect.
Import ssreflect.SsrSyntax.
Require Import separable.

Require Import ssralg.
Import GRing.
Import eqtype.

Zmodule.eqType : zmodType -> eqType


Inductive list (A : Type) : Type := nil | cons of A & list A.

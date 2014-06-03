Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import ssreflect.
Import ssreflect.SsrSyntax.

Inductive list (A : Type) : Type := nil | cons of A & list A.

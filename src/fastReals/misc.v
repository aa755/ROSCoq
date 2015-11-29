Require Import fastReals.interface.
Require Import Coq.ZArith.BinInt.

(*Coq.Numbers.BinNums.*)
Global Instance MinClassZ : MinClass Z := Zmin.
Global Instance MaxClassZ : MaxClass Z := Zmax.

Require Import MathClasses.interfaces.canonical_names.
Require Import MCInstances.

Require Import ROSCOQ.core.
Section TContRFast.
Context  {R:Type} `{IsoFromIR R}.

Instance CastTContRFast : Cast TContR (Time -> R) :=
  λ (tc : TContR) (t : Time), isoFromIR ({tc} t).


End TContRFast.

